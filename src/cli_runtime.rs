//! Shared rule-policy loading and compilation helpers used by the CLI.
//!
//! This module is intentionally separate from `protocol`, which owns the
//! governance protocol state machine. The helpers here are command plumbing:
//! load a rule policy, compile it once, and derive claimant records for CLI
//! inputs that supply claims separately.

use std::{collections::BTreeMap, path::Path};

use crate::{
    Claim, Claimant, CompiledRule, LegitimacyError,
    compiler::{CompileOptions, compile, compile_with_options},
    policy::{ParsedPolicy, load_policy_file},
};

#[derive(Clone)]
pub struct RuntimeContext {
    pub parsed: ParsedPolicy,
    pub compiled: CompiledRule,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RuntimeOptions {
    pub compile: CompileOptions,
}

#[tracing::instrument(skip(policy))]
pub fn load_runtime_context(policy: &Path) -> Result<RuntimeContext, LegitimacyError> {
    load_runtime_context_with_options(policy, RuntimeOptions::default())
}

#[tracing::instrument(skip(policy))]
pub fn load_runtime_context_with_options(
    policy: &Path,
    options: RuntimeOptions,
) -> Result<RuntimeContext, LegitimacyError> {
    let parsed = load_policy_file(policy)?;
    let compiled = compile_parsed_policy_with_options(
        &parsed,
        &parsed.claims,
        &parsed.claimants,
        options.compile,
    )?;

    Ok(RuntimeContext { parsed, compiled })
}

#[tracing::instrument(skip(parsed, claims, claimants))]
pub fn compile_parsed_policy(
    parsed: &ParsedPolicy,
    claims: &[Claim],
    claimants: &[Claimant],
) -> Result<CompiledRule, LegitimacyError> {
    compile(
        &parsed.rule,
        claims,
        &parsed.estate,
        claimants,
        &parsed.family,
    )
}

#[tracing::instrument(skip(parsed, claims, claimants))]
pub fn compile_parsed_policy_with_options(
    parsed: &ParsedPolicy,
    claims: &[Claim],
    claimants: &[Claimant],
    options: CompileOptions,
) -> Result<CompiledRule, LegitimacyError> {
    compile_with_options(
        &parsed.rule,
        claims,
        &parsed.estate,
        claimants,
        &parsed.family,
        options,
    )
}

#[tracing::instrument(skip(parsed, claims))]
pub fn claimants_for_claims(parsed: &ParsedPolicy, claims: &[Claim]) -> Vec<Claimant> {
    let default_priority_class = match parsed.rule.priority_classes.first() {
        Some(priority_class) => priority_class.clone(),
        None => "standard".to_string(),
    };
    let known_claimants = parsed
        .claimants
        .iter()
        .map(|claimant| (claimant.id.clone(), claimant))
        .collect::<BTreeMap<_, _>>();

    claims
        .iter()
        .map(|claim| {
            if let Some(existing) = known_claimants.get(&claim.claimant_id) {
                (*existing).clone()
            } else {
                Claimant {
                    id: claim.claimant_id.clone(),
                    priority_class: default_priority_class.clone(),
                    attributes: BTreeMap::new(),
                }
            }
        })
        .collect()
}
