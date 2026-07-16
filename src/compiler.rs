//! Compiler for legitimacy rule checks.

use std::time::{SystemTime, UNIX_EPOCH};

pub use crate::Family;
use crate::{
    Claim, Claimant, CompiledRule, Estate, LegitimacyError, Rule,
    axioms::diagnostics::{
        consistency::{FullConsistencyOptions, check_full_consistency},
        monotonicity::check_monotonicity,
        solidarity::check_solidarity,
        strategyproofness::check_strategyproofness,
    },
    evaluate_rule,
    ledger::Ledger,
};

/// Compile-time diagnostic options.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CompileOptions {
    pub consistency: FullConsistencyOptions,
}

/// Compile a rule by running all three axiom checkers over the declared family.
///
/// Consistency is skipped (and omitted from `axiom_verdicts`) when
/// `family.reductions` is `false`, since the caller has declared that no
/// reduction sub-problems are in scope.
///
/// Compilation persists the compiled rule to the append-only ledger before
/// returning it. A caller that receives `Ok` can rely on the compilation being
/// recorded for later audit.
#[tracing::instrument(
    skip(rule, claims, estate, claimants, family),
    fields(rule_name = %rule.name, admissible = tracing::field::Empty)
)]
pub fn compile(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    claimants: &[Claimant],
    family: &Family,
) -> Result<CompiledRule, LegitimacyError> {
    compile_with_options(
        rule,
        claims,
        estate,
        claimants,
        family,
        CompileOptions::default(),
    )
}

/// Compile a rule with explicit diagnostic options.
#[tracing::instrument(
    skip(rule, claims, estate, claimants, family),
    fields(rule_name = %rule.name, admissible = tracing::field::Empty)
)]
pub fn compile_with_options(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    claimants: &[Claimant],
    family: &Family,
    options: CompileOptions,
) -> Result<CompiledRule, LegitimacyError> {
    evaluate_rule(rule, claims, estate, "compiler baseline rule evaluation")?;
    let mut axiom_verdicts = Vec::with_capacity(3);

    if family.reductions {
        axiom_verdicts.push(check_full_consistency(
            rule,
            claims,
            estate,
            options.consistency,
        )?);
    }
    axiom_verdicts.push(check_solidarity(
        rule,
        claims,
        estate,
        claimants,
        &family.shocks,
    )?);
    axiom_verdicts.push(check_monotonicity(
        rule,
        claims,
        estate,
        &family.strengthening_deltas,
        family.monotonicity_inversion,
    )?);

    let compiled_rule = CompiledRule {
        name: rule.name.clone(),
        version: rule.version.clone(),
        axiom_verdicts,
        strategyproofness: check_strategyproofness(rule, claims, estate)?,
        family_description: family.describe(),
        compiled_at: unix_timestamp()?,
    };
    tracing::Span::current().record(
        "admissible",
        tracing::field::display(compiled_rule.is_admissible()),
    );

    Ledger::open_default()?.record_compiled_rule(&compiled_rule)?;

    Ok(compiled_rule)
}

fn unix_timestamp() -> Result<String, LegitimacyError> {
    Ok(SystemTime::now()
        .duration_since(UNIX_EPOCH)?
        .as_secs()
        .to_string())
}
