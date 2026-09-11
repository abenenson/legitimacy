use super::*;
use legitimacy::trajectory::codex_exec_v0::{
    CODEX_EXEC_ADAPTER_BINDING_CONTRACT_V0, CODEX_EXEC_CLI_PUBLICATION_BINDING_CONTRACT_V0,
    CODEX_EXEC_FIXTURE_SPEC_BINDING_CONTRACT_V0, CODEX_EXEC_SANITIZED_THREAD_ID_DOMAIN_V0,
    CODEX_EXEC_SANITIZER_BINDING_CONTRACT_V0, codex_exec_adapter_binding_v0,
    codex_exec_cli_publication_binding_v0, codex_exec_fixture_spec_binding_v0,
    codex_exec_sanitizer_binding_v0,
};
use serde::Deserialize;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NormativeContractError {
    Contract,
    SanitizerReconciliation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SanitizerComparison {
    Match,
    Mismatch,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SanitizerStage {
    BoundaryInvoked,
    ReconciliationStarted,
    Compared(SanitizerComparison),
}

type SanitizerObserver<'a> = &'a mut dyn FnMut(SanitizerStage);
type SanitizerVerifier =
    fn(&str, &serde_json::Value, SanitizerObserver<'_>) -> Result<(), NormativeContractError>;
const AUTHORITY_LEAD: &str = "Only the exact statements in the marked contract regions are normative; all remaining text is explanatory and cannot amend or override them.";

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct NormativeContract {
    pub(super) version: String,
    pub(super) facts: Vec<NormativeFact>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(tag = "id", rename_all = "kebab-case", deny_unknown_fields)]
pub(super) enum NormativeFact {
    Bindings {
        adapter: BindingFact,
        sanitizer: BindingFact,
        sanitizer_sources: Vec<String>,
        cli_publication: BindingFact,
        fixture_spec: BindingFact,
    },
    Entropy {
        platform: String,
        source: String,
        flags: String,
        nonce_bytes: u64,
        fill: String,
        reject: String,
    },
    ProcessFailurePrecedence {
        primary: Vec<String>,
        live_descendant: String,
        cleanup: String,
        cleanup_dominates: Vec<String>,
        success_requires: Vec<String>,
    },
    SanitizedIdentity {
        domain: String,
        inputs: Vec<String>,
        projection: Vec<String>,
    },
    AdaptationFlow {
        steps: Vec<String>,
    },
    AnonymousPublication {
        temporary: String,
        mode: String,
        verification: Vec<String>,
        durability: Vec<String>,
    },
    PairOrder {
        precondition: String,
        phases: Vec<String>,
    },
    CommitPoint {
        operation: String,
        replacement: String,
        point: String,
    },
    PublicationUncertainty {
        pre_link: String,
        post_link: String,
        classes: Vec<String>,
        cleanup: String,
    },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct BindingFact {
    identity: String,
    domain: String,
    scopes: Vec<String>,
}

pub(super) fn load_normative_contract(
    build: &serde_json::Value,
) -> Result<NormativeContract, NormativeContractError> {
    serde_json::from_value(build["normative_contract"].clone())
        .map_err(|_| NormativeContractError::Contract)
}

pub(super) fn fact_id(fact: &NormativeFact) -> &'static str {
    match fact {
        NormativeFact::Bindings { .. } => "bindings",
        NormativeFact::Entropy { .. } => "entropy",
        NormativeFact::ProcessFailurePrecedence { .. } => "process-failure-precedence",
        NormativeFact::SanitizedIdentity { .. } => "sanitized-identity",
        NormativeFact::AdaptationFlow { .. } => "adaptation-flow",
        NormativeFact::AnonymousPublication { .. } => "anonymous-publication",
        NormativeFact::PairOrder { .. } => "pair-order",
        NormativeFact::CommitPoint { .. } => "commit-point",
        NormativeFact::PublicationUncertainty { .. } => "publication-uncertainty",
    }
}

pub(super) fn marker(id: &str, edge: &str) -> String {
    format!("<!-- codex-exec-v0-contract:{id}:{edge} -->")
}

fn code_list(values: &[String]) -> String {
    values
        .iter()
        .map(|value| format!("`{value}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn render_fact(fact: &NormativeFact) -> String {
    match fact {
        NormativeFact::Bindings {
            adapter,
            sanitizer,
            sanitizer_sources,
            cli_publication,
            fixture_spec,
        } => format!(
            "Binding contract: `{}` uses domain\n\
             `{}` and scopes\n\
             {}; `{}` uses domain\n\
             `{}` and scopes\n\
             {}; `{}` uses\n\
             domain\n\
             `{}` and\n\
             scopes {}; and\n\
             `{}` uses domain\n\
             `{}` and scopes\n\
             {}.\n\
             Sanitizer registry contract: the complete ordered `sanitizer` registry contains\n\
             {}.",
            adapter.identity,
            adapter.domain,
            code_list(&adapter.scopes),
            sanitizer.identity,
            sanitizer.domain,
            code_list(&sanitizer.scopes),
            cli_publication.identity,
            cli_publication.domain,
            code_list(&cli_publication.scopes),
            fixture_spec.identity,
            fixture_spec.domain,
            code_list(&fixture_spec.scopes),
            code_list(sanitizer_sources),
        ),
        NormativeFact::Entropy {
            platform,
            source,
            flags,
            nonce_bytes,
            fill,
            reject,
        } => format!(
            "Entropy contract: on {platform}, a production nonce is {nonce_bytes} bytes filled by\n\
             `{source}` with `{flags}` flags; the fill policy is\n\
             `{fill}`, and the rejection policy is\n\
             `{reject}`."
        ),
        NormativeFact::ProcessFailurePrecedence {
            primary,
            live_descendant,
            cleanup,
            cleanup_dominates,
            success_requires,
        } => format!(
            "Process failure contract: after complete cleanup, primary precedence is\n\
             {},\n\
             {}.\n\
             `{}` means `{live_descendant}`;\n\
             `{cleanup}` dominates for {},\n\
             {}. Success requires\n\
             {}.",
            code_list(&primary[..3]),
            code_list(&primary[3..]),
            primary[5],
            code_list(&cleanup_dominates[..1]),
            code_list(&cleanup_dominates[1..]),
            code_list(success_requires),
        ),
        NormativeFact::SanitizedIdentity {
            domain,
            inputs,
            projection,
        } => format!(
            "Sanitized identity contract: domain\n\
             `{domain}` hashes\n\
             {} and projects the digest as\n\
             {}.",
            code_list(inputs),
            code_list(projection),
        ),
        NormativeFact::AdaptationFlow { steps } => format!(
            "Adaptation flow contract: the ordered steps are {},\n\
             {}, {}, {},\n\
             {}, {},\n\
             {}.",
            code_list(&steps[0..1]),
            code_list(&steps[1..2]),
            code_list(&steps[2..3]),
            code_list(&steps[3..4]),
            code_list(&steps[4..5]),
            code_list(&steps[5..6]),
            code_list(&steps[6..7]),
        ),
        NormativeFact::AnonymousPublication {
            temporary,
            mode,
            verification,
            durability,
        } => format!(
            "Publication staging contract: temporary storage is `{temporary}`\n\
             with mode `{mode}`; checks are {},\n\
             {}, followed by {}.",
            code_list(&verification[..4]),
            code_list(&verification[4..]),
            code_list(durability),
        ),
        NormativeFact::PairOrder {
            precondition,
            phases,
        } => format!(
            "Pair order contract: the precondition `{precondition}` occurs before all six\n\
             filesystem phases; the phases are {}.",
            code_list(phases),
        ),
        NormativeFact::CommitPoint {
            operation,
            replacement,
            point,
        } => format!(
            "Commit contract: `{operation}` uses `{replacement}` replacement semantics, and the\n\
             commit point is `{point}`."
        ),
        NormativeFact::PublicationUncertainty {
            pre_link,
            post_link,
            classes,
            cleanup,
        } => format!(
            "Uncertainty contract: before commit, `{pre_link}`; after commit,\n\
             `{post_link}` with classes\n\
             {},\n\
             {}; cleanup is `{cleanup}`.",
            code_list(&classes[..2]),
            code_list(&classes[2..]),
        ),
    }
}

pub(super) fn exact_region(fact: &NormativeFact) -> String {
    let id = fact_id(fact);
    format!(
        "{}\n{}\n{}",
        marker(id, "begin"),
        render_fact(fact),
        marker(id, "end")
    )
}

fn contract_is_renderable(contract: &NormativeContract) -> bool {
    contract.facts.iter().all(|fact| match fact {
        NormativeFact::AdaptationFlow { steps } => steps.len() == 7,
        NormativeFact::ProcessFailurePrecedence {
            primary,
            cleanup_dominates,
            success_requires,
            ..
        } => primary.len() == 6 && cleanup_dominates.len() == 3 && success_requires.len() == 2,
        NormativeFact::AnonymousPublication {
            verification,
            durability,
            ..
        } => verification.len() == 5 && durability.len() == 2,
        NormativeFact::PairOrder { phases, .. } => phases.len() == 6,
        NormativeFact::PublicationUncertainty { classes, .. } => classes.len() == 3,
        _ => true,
    })
}

fn verify_marker_topology(
    document: &str,
    contract: &NormativeContract,
) -> Result<(), NormativeContractError> {
    let expected = contract
        .facts
        .iter()
        .flat_map(|fact| [marker(fact_id(fact), "begin"), marker(fact_id(fact), "end")])
        .collect::<Vec<_>>();
    let actual = document
        .lines()
        .filter(|line| line.starts_with("<!-- codex-exec-v0-contract:"))
        .map(str::to_string)
        .collect::<Vec<_>>();
    if actual != expected
        || contract
            .facts
            .iter()
            .any(|fact| document.matches(&exact_region(fact)).count() != 1)
    {
        return Err(NormativeContractError::Contract);
    }
    let mut explanatory = document.to_string();
    for fact in &contract.facts {
        explanatory = explanatory.replacen(&exact_region(fact), "", 1);
    }
    if explanatory.matches(AUTHORITY_LEAD).count() != 1 {
        return Err(NormativeContractError::Contract);
    }
    explanatory = explanatory.replacen(AUTHORITY_LEAD, "", 1);
    if explanatory.to_ascii_lowercase().contains("normative") {
        return Err(NormativeContractError::Contract);
    }
    Ok(())
}

fn documented_sanitizer_sources(document: &str) -> Result<Vec<String>, NormativeContractError> {
    const LEAD: &str =
        "Sanitizer registry contract: the complete ordered `sanitizer` registry contains\n";
    const TAIL: &str = ".\n<!-- codex-exec-v0-contract:bindings:end -->";
    if document.matches(LEAD).count() != 1 {
        return Err(NormativeContractError::Contract);
    }
    let (_, remainder) = document
        .split_once(LEAD)
        .ok_or(NormativeContractError::Contract)?;
    let (list, _) = remainder
        .split_once(TAIL)
        .ok_or(NormativeContractError::Contract)?;
    list.split(", ")
        .map(|entry| {
            entry
                .strip_prefix('`')
                .and_then(|entry| entry.strip_suffix('`'))
                .filter(|entry| !entry.is_empty() && !entry.contains('/'))
                .map(str::to_string)
                .ok_or(NormativeContractError::Contract)
        })
        .collect()
}

pub(super) fn verify_sanitizer_registry_contract(
    document: &str,
    build: &serde_json::Value,
) -> Result<(), NormativeContractError> {
    let mut observer = |_| {};
    verify_sanitizer_registry_boundary(document, build, &mut observer)
}

fn verify_sanitizer_registry_boundary(
    document: &str,
    build: &serde_json::Value,
    observer: SanitizerObserver<'_>,
) -> Result<(), NormativeContractError> {
    observer(SanitizerStage::BoundaryInvoked);
    reconcile_sanitizer_registry_contract(document, build, observer)
}

fn reconcile_sanitizer_registry_contract(
    document: &str,
    build: &serde_json::Value,
    observer: SanitizerObserver<'_>,
) -> Result<(), NormativeContractError> {
    observer(SanitizerStage::ReconciliationStarted);
    let contract = load_normative_contract(build)
        .map_err(|_| NormativeContractError::SanitizerReconciliation)?;
    if !contract_is_renderable(&contract) {
        return Err(NormativeContractError::SanitizerReconciliation);
    }
    verify_marker_topology(document, &contract)
        .map_err(|_| NormativeContractError::SanitizerReconciliation)?;
    let Some(NormativeFact::Bindings {
        sanitizer_sources, ..
    }) = contract.facts.first()
    else {
        return Err(NormativeContractError::SanitizerReconciliation);
    };
    let documented_sources = documented_sanitizer_sources(document)
        .map_err(|_| NormativeContractError::SanitizerReconciliation)?;
    let independent_paths = crate::source_bindings::independent_sanitizer_only_paths();
    let independent_sources = independent_paths
        .iter()
        .map(|path| {
            path.rsplit('/')
                .next()
                .filter(|source| !source.is_empty())
                .ok_or(NormativeContractError::SanitizerReconciliation)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let comparison =
        if documented_sources == *sanitizer_sources && documented_sources == independent_sources {
            SanitizerComparison::Match
        } else {
            SanitizerComparison::Mismatch
        };
    observer(SanitizerStage::Compared(comparison));
    match comparison {
        SanitizerComparison::Match => Ok(()),
        SanitizerComparison::Mismatch => Err(NormativeContractError::SanitizerReconciliation),
    }
}

fn path_last(path: &syn::Path) -> Option<String> {
    path.segments
        .last()
        .map(|segment| segment.ident.to_string())
}

fn pat_path_last(pattern: &syn::Pat) -> Option<String> {
    let syn::Pat::Path(pattern) = pattern else {
        return None;
    };
    path_last(&pattern.path)
}

fn impl_self_is(implementation: &syn::ItemImpl, expected: &str) -> bool {
    let syn::Type::Path(self_type) = implementation.self_ty.as_ref() else {
        return false;
    };
    path_last(&self_type.path).as_deref() == Some(expected)
}

fn final_match(function: &syn::ImplItemFn) -> Option<&syn::ExprMatch> {
    let syn::Stmt::Expr(syn::Expr::Match(expression), _) = function.block.stmts.last()? else {
        return None;
    };
    Some(expression)
}

fn extract_process_primary_order(
    process_sources: &[ProcessSource<'_>],
    adapter_error: &str,
) -> Result<Vec<String>, NormativeContractError> {
    let adapter_error =
        syn::parse_file(adapter_error).map_err(|_| NormativeContractError::Contract)?;
    let mut precedence = None;
    let mut failure_codes = std::collections::BTreeMap::new();
    let mut primary_impls = 0;
    let mut code_functions = 0;
    for process_source in verified_process_sources(process_sources)? {
        let source =
            syn::parse_file(process_source.source).map_err(|_| NormativeContractError::Contract)?;
        for implementation in source.items.iter().filter_map(|item| match item {
            syn::Item::Impl(implementation)
                if impl_self_is(implementation, "PrimaryCaptureFailure") =>
            {
                Some(implementation)
            }
            _ => None,
        }) {
            if process_source.label != "process_capture_supervision" {
                return Err(NormativeContractError::Contract);
            }
            primary_impls += 1;
            for item in &implementation.items {
                match item {
                    syn::ImplItem::Const(constant) if constant.ident == "PRECEDENCE" => {
                        let syn::Expr::Array(array) = &constant.expr else {
                            return Err(NormativeContractError::Contract);
                        };
                        let variants = array
                            .elems
                            .iter()
                            .map(|expression| {
                                let syn::Expr::Path(path) = expression else {
                                    return Err(NormativeContractError::Contract);
                                };
                                path_last(&path.path).ok_or(NormativeContractError::Contract)
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        if precedence.replace(variants).is_some() {
                            return Err(NormativeContractError::Contract);
                        }
                    }
                    syn::ImplItem::Fn(function) if function.sig.ident == "code" => {
                        code_functions += 1;
                        let matched =
                            final_match(function).ok_or(NormativeContractError::Contract)?;
                        for arm in &matched.arms {
                            let variant =
                                pat_path_last(&arm.pat).ok_or(NormativeContractError::Contract)?;
                            let syn::Expr::Path(code) = arm.body.as_ref() else {
                                return Err(NormativeContractError::Contract);
                            };
                            let code =
                                path_last(&code.path).ok_or(NormativeContractError::Contract)?;
                            if failure_codes.insert(variant, code).is_some() {
                                return Err(NormativeContractError::Contract);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    if primary_impls != 1 || code_functions != 1 {
        return Err(NormativeContractError::Contract);
    }

    let mut code_spellings = std::collections::BTreeMap::new();
    for implementation in adapter_error.items.iter().filter_map(|item| match item {
        syn::Item::Impl(implementation) if impl_self_is(implementation, "AdapterErrorCodeV0") => {
            Some(implementation)
        }
        _ => None,
    }) {
        for item in &implementation.items {
            let syn::ImplItem::Fn(function) = item else {
                continue;
            };
            if function.sig.ident != "as_str" {
                continue;
            }
            let matched = final_match(function).ok_or(NormativeContractError::Contract)?;
            for arm in &matched.arms {
                let code = pat_path_last(&arm.pat).ok_or(NormativeContractError::Contract)?;
                let syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(spelling),
                    ..
                }) = arm.body.as_ref()
                else {
                    return Err(NormativeContractError::Contract);
                };
                if code_spellings.insert(code, spelling.value()).is_some() {
                    return Err(NormativeContractError::Contract);
                }
            }
        }
    }

    precedence
        .ok_or(NormativeContractError::Contract)?
        .into_iter()
        .map(|variant| {
            let code = failure_codes
                .get(&variant)
                .ok_or(NormativeContractError::Contract)?;
            code_spellings
                .get(code)
                .cloned()
                .ok_or(NormativeContractError::Contract)
        })
        .collect()
}

#[derive(Clone, Copy)]
pub(super) struct ProcessSource<'a> {
    pub(super) label: &'a str,
    pub(super) path: &'a str,
    pub(super) source: &'a str,
}

pub(super) const PROCESS_SOURCE_IDENTITIES: [(&str, &str); 3] = [
    (
        "process_capture_supervisor",
        "src/trajectory/codex_exec_v0/process_capture_supervisor.rs",
    ),
    (
        "process_capture_supervision",
        "src/trajectory/codex_exec_v0/process_capture_supervision.rs",
    ),
    (
        "process_capture_cleanup",
        "src/trajectory/codex_exec_v0/process_capture_cleanup.rs",
    ),
];

fn verified_process_sources<'a>(
    sources: &'a [ProcessSource<'a>],
) -> Result<&'a [ProcessSource<'a>], NormativeContractError> {
    if sources.len() != PROCESS_SOURCE_IDENTITIES.len()
        || sources
            .iter()
            .map(|source| (source.label, source.path))
            .collect::<Vec<_>>()
            != PROCESS_SOURCE_IDENTITIES
    {
        return Err(NormativeContractError::Contract);
    }
    for source in sources {
        syn::parse_file(source.source).map_err(|_| NormativeContractError::Contract)?;
    }
    Ok(sources)
}

fn process_fragment_count(
    sources: &[ProcessSource<'_>],
    fragment: &str,
) -> Result<usize, NormativeContractError> {
    Ok(verified_process_sources(sources)?
        .iter()
        .map(|source| source.source.matches(fragment).count())
        .sum())
}

#[derive(Clone, Copy)]
pub(super) struct NormativeImplementation<'a> {
    pub(super) sanitizer: &'a str,
    pub(super) nonce: &'a str,
    pub(super) trajectory: &'a str,
    pub(super) linux_output: &'a str,
    pub(super) transaction: &'a str,
    pub(super) process_sources: &'a [ProcessSource<'a>],
    pub(super) adapter_error: &'a str,
}

pub(super) fn verify_normative_contract(
    document: &str,
    build: &serde_json::Value,
    implementation: NormativeImplementation<'_>,
) -> Result<(), NormativeContractError> {
    let mut observer = |_| {};
    verify_normative_contract_with(
        document,
        build,
        implementation,
        verify_sanitizer_registry_boundary,
        &mut observer,
    )
}

pub(super) fn verify_normative_contract_observed(
    document: &str,
    build: &serde_json::Value,
    implementation: NormativeImplementation<'_>,
    observer: SanitizerObserver<'_>,
) -> Result<(), NormativeContractError> {
    verify_normative_contract_with(
        document,
        build,
        implementation,
        verify_sanitizer_registry_boundary,
        observer,
    )
}

fn verify_normative_contract_with(
    document: &str,
    build: &serde_json::Value,
    implementation: NormativeImplementation<'_>,
    sanitizer_verifier: SanitizerVerifier,
    observer: SanitizerObserver<'_>,
) -> Result<(), NormativeContractError> {
    let contract = load_normative_contract(build)?;
    if contract.version != "0"
        || contract.facts.iter().map(fact_id).collect::<Vec<_>>()
            != vec![
                "bindings",
                "entropy",
                "process-failure-precedence",
                "sanitized-identity",
                "adaptation-flow",
                "anonymous-publication",
                "pair-order",
                "commit-point",
                "publication-uncertainty",
            ]
        || !contract_is_renderable(&contract)
    {
        return Err(NormativeContractError::Contract);
    }
    verify_marker_topology(document, &contract)?;
    sanitizer_verifier(document, build, observer)?;
    verify_normative_implementation(&contract, implementation)
}

fn verify_normative_implementation(
    contract: &NormativeContract,
    implementation: NormativeImplementation<'_>,
) -> Result<(), NormativeContractError> {
    let NormativeFact::Bindings {
        adapter,
        sanitizer: sanitizer_binding,
        cli_publication,
        fixture_spec,
        ..
    } = &contract.facts[0]
    else {
        return Err(NormativeContractError::Contract);
    };
    let contracts = [
        (
            CODEX_EXEC_ADAPTER_BINDING_CONTRACT_V0,
            codex_exec_adapter_binding_v0(),
            adapter,
        ),
        (
            CODEX_EXEC_SANITIZER_BINDING_CONTRACT_V0,
            codex_exec_sanitizer_binding_v0(),
            sanitizer_binding,
        ),
        (
            CODEX_EXEC_CLI_PUBLICATION_BINDING_CONTRACT_V0,
            codex_exec_cli_publication_binding_v0(),
            cli_publication,
        ),
        (
            CODEX_EXEC_FIXTURE_SPEC_BINDING_CONTRACT_V0,
            codex_exec_fixture_spec_binding_v0(),
            fixture_spec,
        ),
    ];
    for (implementation, artifact, fact) in contracts {
        if artifact.identity != implementation.identity
            || fact.identity != implementation.identity
            || fact.domain != implementation.framing_domain
            || fact.scopes
                != implementation
                    .registered_scopes
                    .iter()
                    .map(|scope| (*scope).to_string())
                    .collect::<Vec<_>>()
        {
            return Err(NormativeContractError::Contract);
        }
    }
    let NormativeFact::Entropy {
        platform,
        source,
        flags,
        nonce_bytes,
        fill,
        reject,
    } = &contract.facts[1]
    else {
        return Err(NormativeContractError::Contract);
    };
    if (
        platform.as_str(),
        source.as_str(),
        flags.as_str(),
        *nonce_bytes,
        fill.as_str(),
        reject.as_str(),
    ) != (
        "Linux",
        "rustix::rand::getrandom",
        "empty",
        32,
        "retry-interrupted-accept-bounded-partial",
        "unsupported-platform-zero-oversized-failed-all-zero",
    ) {
        return Err(NormativeContractError::Contract);
    }
    if direct_call_argument_profiles(implementation.nonce, "rustix::rand::getrandom")
        .map_err(|_| NormativeContractError::Contract)?
        != vec![compact_profile(&[
            "target",
            "rustix::rand::GetRandomFlags::empty()",
        ])]
    {
        return Err(NormativeContractError::Contract);
    }

    let NormativeFact::ProcessFailurePrecedence {
        primary,
        live_descendant,
        cleanup,
        cleanup_dominates,
        success_requires,
    } = &contract.facts[2]
    else {
        return Err(NormativeContractError::Contract);
    };
    if primary
        != &[
            "capture-stdout-overflow",
            "capture-stderr-overflow",
            "capture-stdin",
            "stream-state",
            "capture-timeout",
            "capture-live-descendant",
        ]
        || live_descendant != "known-main-status-with-fresh-live-owned-descendant"
        || cleanup != "capture-cleanup"
        || cleanup_dominates
            != &[
                "cleanup-operation-error",
                "worker-join-uncertainty",
                "final-absence-unproven",
            ]
        || success_requires != &["fresh-process-tree-absence", "all-workers-complete"]
        || extract_process_primary_order(
            implementation.process_sources,
            implementation.adapter_error,
        )? != *primary
        || process_fragment_count(
            implementation.process_sources,
            "if cleanup_uncertain {\n        SupervisionDecision::CleanupUncertain",
        )? != 1
        || process_fragment_count(
            implementation.process_sources,
            "cleanup.is_ok() && !joined.join_uncertain",
        )? != 1
        || process_fragment_count(
            implementation.process_sources,
            "if uncertain || status.is_none() || !absent",
        )? != 1
        || process_fragment_count(implementation.process_sources, "if !owned.fresh_absence()?")?
            != 1
    {
        return Err(NormativeContractError::Contract);
    }

    let NormativeFact::SanitizedIdentity {
        domain,
        inputs,
        projection,
    } = &contract.facts[3]
    else {
        return Err(NormativeContractError::Contract);
    };
    if domain != CODEX_EXEC_SANITIZED_THREAD_ID_DOMAIN_V0
        || inputs.as_slice() != ["asserted-nonce-source-label", "nonce-bytes-32"]
        || projection.as_slice() != ["uuid-version-7", "rfc-variant", "canonical-lowercase"]
    {
        return Err(NormativeContractError::Contract);
    }
    if direct_call_argument_profiles(implementation.sanitizer, "crate::trajectory::framed_sha256")
        .map_err(|_| NormativeContractError::Contract)?
        != vec![compact_profile(&[
            "CODEX_EXEC_SANITIZED_THREAD_ID_DOMAIN_V0",
            "&[nonce.asserted_source().label().as_bytes(),nonce.bytes()]",
        ])]
    {
        return Err(NormativeContractError::Contract);
    }

    let NormativeFact::AdaptationFlow { steps } = &contract.facts[4] else {
        return Err(NormativeContractError::Contract);
    };
    if steps.as_slice()
        != [
            "adapt-parent",
            "sanitize-child",
            "adapt-exact-child",
            "build-owner-private-sidecar",
            "consume-publication-authority",
            "independently-readapt-pair",
            "begin-filesystem-publication",
        ]
    {
        return Err(NormativeContractError::Contract);
    }
    verify_trajectory_route_shape(implementation.trajectory)
        .map_err(|_| NormativeContractError::Contract)?;

    let NormativeFact::AnonymousPublication {
        temporary,
        mode,
        verification,
        durability,
    } = &contract.facts[5]
    else {
        return Err(NormativeContractError::Contract);
    };
    if temporary != "same-directory-o-tmpfile"
        || mode != "0600"
        || verification.as_slice() != ["owner", "type", "link-count", "content", "stable-metadata"]
        || durability.as_slice() != ["sync-file", "sync-directory"]
    {
        return Err(NormativeContractError::Contract);
    }
    verify_linux_output_route_shape(implementation.linux_output)
        .map_err(|_| NormativeContractError::Contract)?;

    let NormativeFact::PairOrder {
        precondition,
        phases,
    } = &contract.facts[6]
    else {
        return Err(NormativeContractError::Contract);
    };
    let extracted = extract_transaction_pair_order(implementation.transaction)
        .map_err(|_| NormativeContractError::Contract)?;
    if precondition != &extracted.precondition || phases != &extracted.phases {
        return Err(NormativeContractError::Contract);
    }
    verify_transaction_route_shape(implementation.transaction)
        .map_err(|_| NormativeContractError::Contract)?;

    let NormativeFact::CommitPoint {
        operation,
        replacement,
        point,
    } = &contract.facts[7]
    else {
        return Err(NormativeContractError::Contract);
    };
    if (operation.as_str(), replacement.as_str(), point.as_str())
        != ("linkat", "no-clobber", "successful-link")
    {
        return Err(NormativeContractError::Contract);
    }

    let NormativeFact::PublicationUncertainty {
        pre_link,
        post_link,
        classes,
        cleanup,
    } = &contract.facts[8]
    else {
        return Err(NormativeContractError::Contract);
    };
    if pre_link != "no-created-final-name"
        || post_link != "linked-name-may-remain-on-failure"
        || classes.as_slice()
            != [
                "output-identity-uncertain",
                "output-integrity-uncertain",
                "durability-uncertain",
            ]
        || cleanup != "do-not-remove-linked-name"
    {
        return Err(NormativeContractError::Contract);
    }
    Ok(())
}

pub(super) fn verify_pair_order_contract(
    document: &str,
    build: &serde_json::Value,
    transaction: &str,
) -> Result<(), NormativeContractError> {
    let contract = load_normative_contract(build)?;
    if !contract_is_renderable(&contract) {
        return Err(NormativeContractError::Contract);
    }
    verify_marker_topology(document, &contract)?;
    let NormativeFact::PairOrder {
        precondition,
        phases,
    } = &contract.facts[6]
    else {
        return Err(NormativeContractError::Contract);
    };
    let extracted = extract_transaction_pair_order(transaction)
        .map_err(|_| NormativeContractError::Contract)?;
    if precondition != &extracted.precondition || phases != &extracted.phases {
        return Err(NormativeContractError::Contract);
    }
    Ok(())
}
