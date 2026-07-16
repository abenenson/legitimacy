//! `HarnessPolicy` trait — uniform interface for modeling agent harnesses
//! as legitimacy governance policies.
//!
//! An agent harness (Claude Agent SDK, Codex, pi-agent, or any custom runner) has an
//! authorization policy: some set of tool invocations are governed by a rule that
//! decides who gets access, how much, and under what conditions.
//!
//! Implementing `HarnessPolicy` for a harness lets legitimacy:
//! - Compile the harness rule and check all three graph-diagnostic axioms
//! - Run paradox detection
//! - Produce promotion certificates for specific invocations
//!
//! This trait is the extension point for harness-specific governance audits.

use crate::{
    Claim, Claimant, CompiledRule, Estate, LegitimacyError, Rule,
    compiler::{Family, compile},
    paradox::{ParadoxViolation, run_paradox_suite},
};

/// A governable agent harness.
///
/// Implementors declare their rule, estate, claimants, claims, and perturbation
/// family.  The trait provides default implementations of `compile` and
/// `paradoxes` so callers get axiom verdicts and paradox diagnostics without
/// additional boilerplate.
pub trait HarnessPolicy {
    /// Human-readable name for this harness (e.g. `"claude-agent-sdk-permissions"`).
    fn name(&self) -> &str;

    /// The estate: total available authorization budget.
    fn estate(&self) -> Result<Estate, LegitimacyError>;

    /// The claimants: the agents or invocations governed by this harness.
    fn claimants(&self) -> Vec<Claimant>;

    /// The claims: each claimant's measured authorization strength.
    fn claims(&self) -> Result<Vec<Claim>, LegitimacyError>;

    /// The allocation rule that decides how the estate is distributed.
    fn rule(&self) -> Rule;

    /// The perturbation family the harness claims to govern lawfully.
    fn family(&self) -> Result<Family, LegitimacyError>;

    /// Compile the harness rule and check all three axioms.
    ///
    /// Returns a `CompiledRule` with axiom verdicts.  The rule is admissible
    /// if all three axioms pass over the declared family.
    fn compile(&self) -> Result<CompiledRule, LegitimacyError> {
        let claims = self.claims()?;
        let estate = self.estate()?;
        let family = self.family()?;
        compile(&self.rule(), &claims, &estate, &self.claimants(), &family)
    }

    /// Run the paradox detection suite on this harness.
    ///
    /// Returns a (possibly empty) list of structural paradoxes.
    fn paradoxes(&self) -> Result<Vec<ParadoxViolation>, LegitimacyError> {
        let claims = self.claims()?;
        let estate = self.estate()?;
        run_paradox_suite(&self.rule(), &claims, &estate, &self.claimants())
    }
}
