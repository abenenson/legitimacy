//! TOML-based parser for `*.rule.toml` rule policy files.

use std::{collections::BTreeMap, fs, path::Path};

use serde::Deserialize;

use crate::{
    Claim, Claimant, CompiledRule, Estate, Family, LegitimacyError, PositiveStrength, Rule,
    RuleSpec, compiler::compile,
};

const INLINE_POLICY_CONTEXT: &str = "<inline rule policy>";
const SUPPORTED_REDUCTION: &str = "remove_any_single_claimant";

/// Raw `*.rule.toml` policy specification.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct PolicySpec {
    pub rule: PolicyRuleSpec,
    pub claimants: ClaimantsSpec,
    pub estate: EstateSpec,
    pub claims: ClaimsSpec,
    pub priority_classes: BTreeMap<String, PriorityClassSpec>,
    #[serde(default)]
    pub instances: Vec<InstanceSpec>,
    pub family: FamilySpec,
}

/// Rule metadata declared in a `*.rule.toml` file.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct PolicyRuleSpec {
    pub name: String,
    pub version: String,
    #[serde(default = "default_rule_kind")]
    pub kind: String,
}

/// Claimant schema metadata declared in a `*.rule.toml` file.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct ClaimantsSpec {
    #[serde(rename = "type")]
    pub r#type: String,
    pub id_field: String,
}

/// Estate metadata declared in a `*.rule.toml` file.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct EstateSpec {
    #[serde(rename = "type")]
    pub r#type: String,
    pub total: f64,
    pub unit: String,
}

/// Claim ordering metadata declared in a `*.rule.toml` file.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct ClaimsSpec {
    pub ordering: String,
}

/// Priority class definition declared in a `*.rule.toml` file.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
pub struct PriorityClassSpec {
    pub level: u32,
}

/// A concrete claimant/claim instance declared in a `*.rule.toml` file.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct InstanceSpec {
    pub id: String,
    pub priority_class: String,
    pub strength: f64,
    #[serde(default)]
    pub metrics: BTreeMap<String, f64>,
}

/// Declared perturbation family for axiom checks.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct FamilySpec {
    pub reductions: String,
    pub shocks: Vec<f64>,
    pub strengthening: Vec<f64>,
    /// When `true`, the monotonicity check is inverted: strengthening must not
    /// *increase* allocation.  For safety-clearance rules.  Defaults to `false`.
    #[serde(default)]
    pub monotonicity_inversion: bool,
}

/// Validated runtime bundle the axiom checkers can consume.
#[derive(Clone)]
pub struct ParsedPolicy {
    pub spec: PolicySpec,
    pub rule: Rule,
    pub estate: Estate,
    pub family: Family,
    pub claimants: Vec<Claimant>,
    pub claims: Vec<Claim>,
}

pub type PolicyParseError = LegitimacyError;

impl PolicySpec {
    /// Validate and convert a raw policy spec into the runtime bundle.
    #[tracing::instrument(skip(self))]
    pub fn try_into_parsed(self) -> Result<ParsedPolicy, LegitimacyError> {
        self.try_into_parsed_with_context(INLINE_POLICY_CONTEXT)
    }

    fn try_into_parsed_with_context(
        self,
        context: impl Into<String>,
    ) -> Result<ParsedPolicy, LegitimacyError> {
        let context = context.into();
        validate_policy_spec(&self, &context)?;

        let rule = build_rule(&self.rule, &self.priority_classes, &context)?;
        let (claimants, claims) = if self.instances.is_empty() {
            let claimants = synthesized_claimants(&rule.priority_classes);
            let claims = synthesized_claims(&claimants)?;
            (claimants, claims)
        } else {
            instances_to_runtime(&self.instances, &self.priority_classes, &context)?
        };

        let estate = Estate::new(self.estate.total, self.estate.unit.clone())
            .map_err(|error| LegitimacyError::invalid_policy(&context, error.to_string()))?;
        let family = Family {
            reductions: self.family.reductions == SUPPORTED_REDUCTION,
            shocks: self.family.shocks.clone(),
            strengthening_deltas: self
                .family
                .strengthening
                .iter()
                .copied()
                .map(PositiveStrength::new)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|error| LegitimacyError::invalid_policy(&context, error.to_string()))?,
            monotonicity_inversion: self.family.monotonicity_inversion,
        };

        Ok(ParsedPolicy {
            spec: self,
            rule,
            estate,
            family,
            claimants,
            claims,
        })
    }
}

/// Parse a raw rule policy string into `PolicySpec`.
#[tracing::instrument(skip(input))]
pub fn parse_policy_str(input: &str) -> Result<PolicySpec, LegitimacyError> {
    parse_policy_str_with_context(input, INLINE_POLICY_CONTEXT)
}

/// Parse a `*.rule.toml` file into `PolicySpec`.
#[tracing::instrument(skip(path))]
pub fn parse_policy_file(path: impl AsRef<Path>) -> Result<PolicySpec, LegitimacyError> {
    let path = path.as_ref();
    let context = path.display().to_string();
    let input = fs::read_to_string(path).map_err(|source| LegitimacyError::PolicyRead {
        path: context.clone(),
        source,
    })?;

    parse_policy_str_with_context(&input, context)
}

/// Parse and validate a raw rule policy string into the runtime bundle.
#[tracing::instrument(skip(input))]
pub fn load_policy_str(input: &str) -> Result<ParsedPolicy, LegitimacyError> {
    parse_policy_str(input)?.try_into_parsed()
}

/// Parse and validate a `*.rule.toml` file into the runtime bundle.
#[tracing::instrument(skip(path))]
pub fn load_policy_file(path: impl AsRef<Path>) -> Result<ParsedPolicy, LegitimacyError> {
    let path = path.as_ref();
    let context = path.display().to_string();
    let spec = parse_policy_file(path)?;
    spec.try_into_parsed_with_context(context)
}

/// Parse, validate, and compile a `*.rule.toml` file end-to-end.
#[tracing::instrument(skip(path))]
pub fn compile_policy(path: impl AsRef<Path>) -> Result<CompiledRule, LegitimacyError> {
    let parsed = load_policy_file(path)?;
    compile(
        &parsed.rule,
        &parsed.claims,
        &parsed.estate,
        &parsed.claimants,
        &parsed.family,
    )
}

fn parse_policy_str_with_context(
    input: &str,
    context: impl Into<String>,
) -> Result<PolicySpec, LegitimacyError> {
    let context = context.into();
    toml::from_str(input).map_err(|source| LegitimacyError::PolicyToml { context, source })
}

fn ordered_priority_classes(priority_classes: &BTreeMap<String, PriorityClassSpec>) -> Vec<String> {
    let mut entries: Vec<_> = priority_classes.iter().collect();
    entries.sort_by(|(left_name, left_spec), (right_name, right_spec)| {
        left_spec
            .level
            .cmp(&right_spec.level)
            .then_with(|| left_name.cmp(right_name))
    });

    entries.into_iter().map(|(name, _)| name.clone()).collect()
}

fn build_rule(
    spec: &PolicyRuleSpec,
    priority_classes: &BTreeMap<String, PriorityClassSpec>,
    context: &str,
) -> Result<Rule, LegitimacyError> {
    Ok(Rule {
        name: spec.name.clone(),
        version: spec.version.clone(),
        rule_spec: RuleSpec::declarative(&spec.kind)
            .map_err(|error| LegitimacyError::invalid_policy(context, error.to_string()))?,
        priority_classes: ordered_priority_classes(priority_classes),
    })
}

fn validate_policy_spec(spec: &PolicySpec, context: &str) -> Result<(), LegitimacyError> {
    validate_non_empty(&spec.rule.name, "rule.name", context)?;
    validate_non_empty(&spec.rule.version, "rule.version", context)?;
    validate_non_empty(&spec.rule.kind, "rule.kind", context)?;
    validate_non_empty(&spec.claimants.r#type, "claimants.type", context)?;
    validate_non_empty(&spec.claimants.id_field, "claimants.id_field", context)?;
    validate_non_empty(&spec.estate.r#type, "estate.type", context)?;
    validate_non_empty(&spec.estate.unit, "estate.unit", context)?;
    validate_non_empty(&spec.claims.ordering, "claims.ordering", context)?;

    if !spec.estate.total.is_finite() || spec.estate.total <= 0.0 {
        return Err(LegitimacyError::invalid_policy(
            context,
            format!(
                "estate.total must be a positive finite number, got {}",
                spec.estate.total
            ),
        ));
    }

    if spec.priority_classes.is_empty() {
        return Err(LegitimacyError::invalid_policy(
            context,
            "priority_classes must declare at least one class",
        ));
    }

    if spec.family.reductions != SUPPORTED_REDUCTION {
        return Err(LegitimacyError::invalid_policy(
            context,
            format!(
                "family.reductions '{value}' is unsupported; expected '{SUPPORTED_REDUCTION}'",
                value = spec.family.reductions
            ),
        ));
    }

    validate_positive_values(&spec.family.shocks, "family.shocks", context)?;
    validate_positive_values(&spec.family.strengthening, "family.strengthening", context)?;
    validate_instances(spec, context)?;

    Ok(())
}

fn validate_non_empty(value: &str, field_name: &str, context: &str) -> Result<(), LegitimacyError> {
    if value.trim().is_empty() {
        return Err(LegitimacyError::invalid_policy(
            context,
            format!("{field_name} must not be empty"),
        ));
    }

    Ok(())
}

fn validate_positive_values(
    values: &[f64],
    field_name: &str,
    context: &str,
) -> Result<(), LegitimacyError> {
    if values.is_empty() {
        return Err(LegitimacyError::invalid_policy(
            context,
            format!("{field_name} must contain at least one value"),
        ));
    }

    if let Some(value) = values
        .iter()
        .copied()
        .find(|value| !value.is_finite() || *value <= 0.0)
    {
        return Err(LegitimacyError::invalid_policy(
            context,
            format!("{field_name} must contain only positive finite values, got {value}"),
        ));
    }

    Ok(())
}

fn validate_instances(spec: &PolicySpec, context: &str) -> Result<(), LegitimacyError> {
    let mut seen_ids = std::collections::BTreeSet::new();

    for instance in &spec.instances {
        validate_non_empty(&instance.id, "instances.id", context)?;
        validate_non_empty(
            &instance.priority_class,
            "instances.priority_class",
            context,
        )?;

        if !spec.priority_classes.contains_key(&instance.priority_class) {
            return Err(LegitimacyError::invalid_policy(
                context,
                format!(
                    "instance '{}' references unknown priority class '{}'",
                    instance.id, instance.priority_class
                ),
            ));
        }

        if !instance.strength.is_finite() || instance.strength <= 0.0 {
            return Err(LegitimacyError::invalid_policy(
                context,
                format!(
                    "instance '{}' strength must be a strictly positive finite number, got {}",
                    instance.id, instance.strength
                ),
            ));
        }

        if !seen_ids.insert(instance.id.clone()) {
            return Err(LegitimacyError::invalid_policy(
                context,
                format!("duplicate instance id '{}'", instance.id),
            ));
        }

        for (metric, value) in &instance.metrics {
            validate_non_empty(metric, "instances.metrics key", context)?;
            if !value.is_finite() {
                return Err(LegitimacyError::invalid_policy(
                    context,
                    format!(
                        "instance '{}' metric '{}' must be finite, got {}",
                        instance.id, metric, value
                    ),
                ));
            }
        }
    }

    Ok(())
}

fn instances_to_runtime(
    instances: &[InstanceSpec],
    priority_classes: &BTreeMap<String, PriorityClassSpec>,
    context: &str,
) -> Result<(Vec<Claimant>, Vec<Claim>), LegitimacyError> {
    let mut claimants = Vec::with_capacity(instances.len());
    let mut claims = Vec::with_capacity(instances.len());

    for instance in instances {
        let Some(class_spec) = priority_classes.get(&instance.priority_class) else {
            return Err(LegitimacyError::invalid_policy(
                context,
                format!(
                    "instance '{}' references unknown priority class '{}'",
                    instance.id, instance.priority_class
                ),
            ));
        };

        claimants.push(Claimant {
            id: instance.id.clone(),
            priority_class: instance.priority_class.clone(),
            attributes: BTreeMap::from([("priority_level".to_string(), class_spec.level as f64)]),
        });

        let mut metrics = instance.metrics.clone();
        metrics.insert("priority_level".to_string(), class_spec.level as f64);
        let mut claim = Claim::try_new(instance.id.clone(), instance.strength)
            .map_err(|error| LegitimacyError::invalid_policy(context, error.to_string()))?;
        claim.metrics = metrics;
        claims.push(claim);
    }

    Ok((claimants, claims))
}

fn synthesized_claimants(priority_classes: &[String]) -> Vec<Claimant> {
    let mut claimants = Vec::new();

    // Rule policy files declare a rule family, not a concrete event stream, so
    // end-to-end compilation uses a deterministic witness cohort per class.
    for priority_class in priority_classes {
        for member_index in 0..2 {
            claimants.push(Claimant {
                id: format!("{priority_class}_{}", member_index + 1),
                priority_class: priority_class.clone(),
                attributes: BTreeMap::new(),
            });
        }
    }

    claimants
}

fn synthesized_claims(claimants: &[Claimant]) -> Result<Vec<Claim>, LegitimacyError> {
    claimants
        .iter()
        .enumerate()
        .map(|(index, claimant)| Claim::new(claimant.id.clone(), index as f64 + 1.0))
        .collect()
}

fn default_rule_kind() -> String {
    "proportional".to_string()
}
