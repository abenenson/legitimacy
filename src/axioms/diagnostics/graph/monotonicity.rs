use crate::{
    Counterexample, GovernanceClaim, GovernanceGraph, LegitimacyError, Verdict,
    axioms::{
        binary::BinaryDelta,
        graph::{
            apply_field_delta, claimant_ids, convert_claims, decision_allocation,
            decision_direction, final_decisions, graph_estate,
        },
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AuditMetricPolarity {
    HigherBetter,
    LowerBetter,
    DiagnosticPresence,
}

#[derive(Clone, Debug)]
pub struct AuditMetricPolaritySchema {
    entries: &'static [(&'static str, AuditMetricPolarity)],
}

impl Default for AuditMetricPolaritySchema {
    fn default() -> Self {
        Self {
            entries: AUDIT_METRIC_POLARITY_SCHEMA,
        }
    }
}

impl AuditMetricPolaritySchema {
    pub fn polarity_for(&self, field: &str) -> Option<AuditMetricPolarity> {
        self.entries
            .iter()
            .find_map(|(candidate, polarity)| (*candidate == field).then_some(*polarity))
    }
}

pub const AUDIT_METRIC_POLARITY_SCHEMA: &[(&str, AuditMetricPolarity)] = &[
    ("approval_forbidden", AuditMetricPolarity::LowerBetter),
    ("approval_not_found", AuditMetricPolarity::LowerBetter),
    ("block_reason", AuditMetricPolarity::LowerBetter),
    ("blocked_context", AuditMetricPolarity::LowerBetter),
    (
        "combined_untrusted_suspicion",
        AuditMetricPolarity::LowerBetter,
    ),
    ("blocked", AuditMetricPolarity::LowerBetter),
    ("dangerous_keyword", AuditMetricPolarity::LowerBetter),
    ("dangerous_pattern", AuditMetricPolarity::LowerBetter),
    ("dangerous_user_approved", AuditMetricPolarity::LowerBetter),
    ("dangerous_user_rejected", AuditMetricPolarity::LowerBetter),
    ("dangerous_without_ui", AuditMetricPolarity::LowerBetter),
    ("deployment_context", AuditMetricPolarity::LowerBetter),
    (
        "hook_invalid_or_unsupported",
        AuditMetricPolarity::LowerBetter,
    ),
    ("latency", AuditMetricPolarity::LowerBetter),
    (
        "monitor_validation_failure",
        AuditMetricPolarity::LowerBetter,
    ),
    ("paradox_risk", AuditMetricPolarity::LowerBetter),
    ("policyblocked", AuditMetricPolarity::LowerBetter),
    ("policy_strictness", AuditMetricPolarity::LowerBetter),
    ("risk", AuditMetricPolarity::LowerBetter),
    (
        "trusted_edit_band_suspicion",
        AuditMetricPolarity::LowerBetter,
    ),
    (
        "trusted_edit_top2_suspicion",
        AuditMetricPolarity::LowerBetter,
    ),
    ("trusted_suspicion", AuditMetricPolarity::LowerBetter),
    (
        "trusted_suspicion_defer_band",
        AuditMetricPolarity::LowerBetter,
    ),
    ("trusted_suspicion_top2", AuditMetricPolarity::LowerBetter),
    ("test_failure", AuditMetricPolarity::LowerBetter),
    ("upfront_audit_window", AuditMetricPolarity::LowerBetter),
    ("after_hook", AuditMetricPolarity::HigherBetter),
    ("allowacrossproviders", AuditMetricPolarity::HigherBetter),
    ("allowcrosscontextsend", AuditMetricPolarity::HigherBetter),
    ("allowed", AuditMetricPolarity::HigherBetter),
    ("alloweddecisions", AuditMetricPolarity::HigherBetter),
    ("allowfinalsymlink", AuditMetricPolarity::HigherBetter),
    ("allowlist", AuditMetricPolarity::HigherBetter),
    ("allowlist_match", AuditMetricPolarity::HigherBetter),
    ("allowlistsatisfied", AuditMetricPolarity::HigherBetter),
    ("allowpluginfallback", AuditMetricPolarity::HigherBetter),
    (
        "allowskillpreludeatindex",
        AuditMetricPolarity::HigherBetter,
    ),
    ("allowskills", AuditMetricPolarity::HigherBetter),
    ("allowunsafereplay", AuditMetricPolarity::HigherBetter),
    ("allowwithinprovider", AuditMetricPolarity::HigherBetter),
    ("agent_id", AuditMetricPolarity::HigherBetter),
    ("approval", AuditMetricPolarity::HigherBetter),
    ("approval_policy", AuditMetricPolarity::HigherBetter),
    ("approval_required", AuditMetricPolarity::DiagnosticPresence),
    ("approvalcommandid", AuditMetricPolarity::HigherBetter),
    ("approvalid", AuditMetricPolarity::HigherBetter),
    ("approvalkind", AuditMetricPolarity::HigherBetter),
    ("approvalslug", AuditMetricPolarity::HigherBetter),
    ("approved", AuditMetricPolarity::HigherBetter),
    ("approvedforsession", AuditMetricPolarity::HigherBetter),
    ("analysis_ok", AuditMetricPolarity::HigherBetter),
    ("audit_recorded", AuditMetricPolarity::HigherBetter),
    ("audit_signal", AuditMetricPolarity::HigherBetter),
    ("available", AuditMetricPolarity::HigherBetter),
    ("base_authorization", AuditMetricPolarity::HigherBetter),
    ("baseline", AuditMetricPolarity::HigherBetter),
    ("baseline_allow", AuditMetricPolarity::HigherBetter),
    ("before_hook", AuditMetricPolarity::HigherBetter),
    ("block_threshold", AuditMetricPolarity::HigherBetter),
    ("checkpoint_written", AuditMetricPolarity::HigherBetter),
    (
        "claude_md_always_execute",
        AuditMetricPolarity::HigherBetter,
    ),
    ("completed_turn", AuditMetricPolarity::HigherBetter),
    ("consequential", AuditMetricPolarity::HigherBetter),
    ("content_length", AuditMetricPolarity::HigherBetter),
    ("deny_signal", AuditMetricPolarity::DiagnosticPresence),
    ("denied", AuditMetricPolarity::DiagnosticPresence),
    ("diversity", AuditMetricPolarity::HigherBetter),
    ("durable_trust", AuditMetricPolarity::HigherBetter),
    ("escalated", AuditMetricPolarity::DiagnosticPresence),
    ("escalate_signal", AuditMetricPolarity::DiagnosticPresence),
    ("executed", AuditMetricPolarity::HigherBetter),
    ("execution_skipped", AuditMetricPolarity::DiagnosticPresence),
    ("fallback_selected", AuditMetricPolarity::HigherBetter),
    ("file_edit", AuditMetricPolarity::HigherBetter),
    ("full_access", AuditMetricPolarity::HigherBetter),
    ("hook", AuditMetricPolarity::HigherBetter),
    ("hook_blocks", AuditMetricPolarity::HigherBetter),
    ("hook_event_name", AuditMetricPolarity::HigherBetter),
    ("hook_registration", AuditMetricPolarity::HigherBetter),
    (
        "hook_registration:BeforeToolCall",
        AuditMetricPolarity::HigherBetter,
    ),
    (
        "hook_registration:CodeExecutorApproval",
        AuditMetricPolarity::HigherBetter,
    ),
    (
        "hook_registration:DialoguePolicy",
        AuditMetricPolarity::HigherBetter,
    ),
    (
        "hook_registration:InterruptBeforeTool",
        AuditMetricPolarity::HigherBetter,
    ),
    (
        "hook_registration:PreToolUse",
        AuditMetricPolarity::HigherBetter,
    ),
    (
        "hook_run_is_quiet_success",
        AuditMetricPolarity::HigherBetter,
    ),
    (
        "human_resume_required",
        AuditMetricPolarity::DiagnosticPresence,
    ),
    ("human_review", AuditMetricPolarity::HigherBetter),
    ("interrupt", AuditMetricPolarity::HigherBetter),
    ("invocation_id", AuditMetricPolarity::HigherBetter),
    ("listed", AuditMetricPolarity::HigherBetter),
    ("maxTurns", AuditMetricPolarity::HigherBetter),
    ("memory_id", AuditMetricPolarity::HigherBetter),
    (
        "most_common_answer_score",
        AuditMetricPolarity::HigherBetter,
    ),
    ("needs_approval", AuditMetricPolarity::DiagnosticPresence),
    ("observation_id", AuditMetricPolarity::HigherBetter),
    ("permission", AuditMetricPolarity::HigherBetter),
    ("permission_mode", AuditMetricPolarity::HigherBetter),
    ("permissiongrantscope", AuditMetricPolarity::HigherBetter),
    ("permissions", AuditMetricPolarity::HigherBetter),
    ("patch_applied", AuditMetricPolarity::HigherBetter),
    ("peer_relative", AuditMetricPolarity::HigherBetter),
    ("policy", AuditMetricPolarity::HigherBetter),
    ("policy_cwd", AuditMetricPolarity::HigherBetter),
    ("policy_for_chat", AuditMetricPolarity::HigherBetter),
    ("policy_match", AuditMetricPolarity::HigherBetter),
    ("policy_rule_matched", AuditMetricPolarity::HigherBetter),
    ("permit_signal", AuditMetricPolarity::HigherBetter),
    ("primary_failed", AuditMetricPolarity::DiagnosticPresence),
    ("profile_restricted", AuditMetricPolarity::HigherBetter),
    ("record_id", AuditMetricPolarity::HigherBetter),
    ("refusal_emitted", AuditMetricPolarity::DiagnosticPresence),
    ("reviewdecision", AuditMetricPolarity::HigherBetter),
    ("runtime_roots_readable", AuditMetricPolarity::HigherBetter),
    ("sandbox", AuditMetricPolarity::HigherBetter),
    ("sandbox_policy", AuditMetricPolarity::HigherBetter),
    (
        "sandbox_setup_is_complete",
        AuditMetricPolarity::HigherBetter,
    ),
    ("sandboxpolicy", AuditMetricPolarity::HigherBetter),
    ("sandboxed", AuditMetricPolarity::HigherBetter),
    ("sanitize_context", AuditMetricPolarity::HigherBetter),
    ("scarcity_bonus", AuditMetricPolarity::HigherBetter),
    ("security_allowlist", AuditMetricPolarity::HigherBetter),
    ("sensitive_path", AuditMetricPolarity::HigherBetter),
    (
        "skip_exec_approval",
        AuditMetricPolarity::DiagnosticPresence,
    ),
    ("solve_directly", AuditMetricPolarity::HigherBetter),
    ("specialization_floor", AuditMetricPolarity::HigherBetter),
    ("specialization_penalty", AuditMetricPolarity::HigherBetter),
    ("stdout_taken_over", AuditMetricPolarity::HigherBetter),
    ("strength", AuditMetricPolarity::HigherBetter),
    ("task_id", AuditMetricPolarity::HigherBetter),
    ("tests_run", AuditMetricPolarity::HigherBetter),
    ("tool_call", AuditMetricPolarity::HigherBetter),
    ("tool_ready", AuditMetricPolarity::HigherBetter),
    ("tool_name", AuditMetricPolarity::HigherBetter),
    ("training_context", AuditMetricPolarity::HigherBetter),
    ("unsafe_intent", AuditMetricPolarity::DiagnosticPresence),
    ("word_count", AuditMetricPolarity::HigherBetter),
];

pub fn check_graph_monotonicity(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    deltas: &[BinaryDelta],
) -> Result<Verdict, LegitimacyError> {
    monotonicity_check_via_polarity_schema(
        graph,
        claims,
        deltas,
        &AuditMetricPolaritySchema::default(),
    )
}

pub fn monotonicity_check_via_polarity_schema(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    deltas: &[BinaryDelta],
    schema: &AuditMetricPolaritySchema,
) -> Result<Verdict, LegitimacyError> {
    let original_decisions = final_decisions(graph, claims)?;
    let original_allocation = decision_allocation(claims, &original_decisions)?;
    let original_claims = convert_claims(claims)?;
    let original_estate = graph_estate()?;
    let claimant_ids = claimant_ids(claims);
    let mut perturbations_tested = 0usize;

    for delta in deltas {
        if !delta.delta.is_finite() || delta.delta <= 0.0 {
            continue;
        }

        let improvement_delta = match schema.polarity_for(&delta.field) {
            Some(AuditMetricPolarity::HigherBetter) => delta.delta,
            Some(AuditMetricPolarity::LowerBetter) => -delta.delta,
            Some(AuditMetricPolarity::DiagnosticPresence) => continue,
            None => {
                return Err(LegitimacyError::InvalidGate {
                    gate: delta.field.clone(),
                    message: format!(
                        "metric field '{}' has no schema polarity annotation",
                        delta.field
                    ),
                });
            }
        };

        for index in 0..claims.len() {
            let strengthened_claims = claims
                .iter()
                .enumerate()
                .map(|(claim_index, claim)| {
                    if claim_index == index {
                        apply_field_delta(claim, &delta.field, improvement_delta)
                    } else {
                        Ok(claim.clone())
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            let strengthened_decisions = final_decisions(graph, &strengthened_claims)?;
            let strengthened_allocation =
                decision_allocation(&strengthened_claims, &strengthened_decisions)?;
            perturbations_tested += 1;

            let strengthened_claimant = claims[index].claimant_id.clone();
            for claimant_id in &claimant_ids {
                let before = original_decisions.get(claimant_id).ok_or_else(|| {
                    LegitimacyError::missing_allocation_share(
                        claimant_id.clone(),
                        "graph monotonicity original lookup",
                    )
                })?;
                let after = strengthened_decisions.get(claimant_id).ok_or_else(|| {
                    LegitimacyError::missing_allocation_share(
                        claimant_id.clone(),
                        "graph monotonicity strengthened lookup",
                    )
                })?;

                if decision_direction(before, after) < 0 {
                    return Ok(Verdict::Rejected {
                        axiom: "graph monotonicity".to_string(),
                        counterexample: Counterexample {
                            description: format!(
                                "Improving '{}' on '{}' by {:.2} worsened '{}' from {:?} to {:?}",
                                strengthened_claimant,
                                delta.field,
                                delta.delta,
                                claimant_id,
                                before,
                                after
                            ),
                            original_claims: original_claims.clone(),
                            original_estate: original_estate.clone(),
                            original_allocation: original_allocation.clone(),
                            perturbed_claims: convert_claims(&strengthened_claims)?,
                            perturbed_estate: original_estate.clone(),
                            perturbed_allocation: strengthened_allocation,
                            violation: format!(
                                "Schema-aware improvement of '{}' changed the composed graph so that '{}' became strictly worse at the exit node.",
                                strengthened_claimant, claimant_id
                            ),
                        },
                    });
                }
            }
        }
    }

    Ok(Verdict::Admissible {
        axiom: "graph monotonicity".to_string(),
        perturbations_tested,
    })
}

#[deprecated(note = "compat-only legacy checker; use monotonicity_check_via_polarity_schema")]
pub fn check_graph_monotonicity_positive_delta(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    deltas: &[BinaryDelta],
) -> Result<Verdict, LegitimacyError> {
    let original_decisions = final_decisions(graph, claims)?;
    let original_allocation = decision_allocation(claims, &original_decisions)?;
    let original_claims = convert_claims(claims)?;
    let original_estate = graph_estate()?;
    let claimant_ids = claimant_ids(claims);
    let mut perturbations_tested = 0usize;

    for delta in deltas {
        if !delta.delta.is_finite() || delta.delta <= 0.0 {
            continue;
        }

        for index in 0..claims.len() {
            let strengthened_claims = claims
                .iter()
                .enumerate()
                .map(|(claim_index, claim)| {
                    if claim_index == index {
                        apply_field_delta(claim, &delta.field, delta.delta)
                    } else {
                        Ok(claim.clone())
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            let strengthened_decisions = final_decisions(graph, &strengthened_claims)?;
            let strengthened_allocation =
                decision_allocation(&strengthened_claims, &strengthened_decisions)?;
            perturbations_tested += 1;

            let strengthened_claimant = claims[index].claimant_id.clone();
            for claimant_id in &claimant_ids {
                let before = original_decisions.get(claimant_id).ok_or_else(|| {
                    LegitimacyError::missing_allocation_share(
                        claimant_id.clone(),
                        "graph monotonicity original lookup",
                    )
                })?;
                let after = strengthened_decisions.get(claimant_id).ok_or_else(|| {
                    LegitimacyError::missing_allocation_share(
                        claimant_id.clone(),
                        "graph monotonicity strengthened lookup",
                    )
                })?;

                if decision_direction(before, after) < 0 {
                    return Ok(Verdict::Rejected {
                        axiom: "graph monotonicity".to_string(),
                        counterexample: Counterexample {
                            description: format!(
                                "Strengthening '{}' on '{}' by {:.2} worsened '{}' from {:?} to {:?}",
                                strengthened_claimant,
                                delta.field,
                                delta.delta,
                                claimant_id,
                                before,
                                after
                            ),
                            original_claims: original_claims.clone(),
                            original_estate: original_estate.clone(),
                            original_allocation: original_allocation.clone(),
                            perturbed_claims: convert_claims(&strengthened_claims)?,
                            perturbed_estate: original_estate.clone(),
                            perturbed_allocation: strengthened_allocation,
                            violation: format!(
                                "Strengthening '{}' changed the composed graph so that '{}' became strictly worse at the exit node.",
                                strengthened_claimant, claimant_id
                            ),
                        },
                    });
                }
            }
        }
    }

    Ok(Verdict::Admissible {
        axiom: "graph monotonicity".to_string(),
        perturbations_tested,
    })
}

#[cfg(test)]
mod tests {
    use super::check_graph_monotonicity;
    use crate::{
        Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceNode, GraphBuilder,
        NodeId, Verdict, axioms::binary::BinaryDelta,
    };
    use std::collections::BTreeMap;

    #[test]
    fn composed_graph_can_fail_monotonicity_via_new_competitor() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(threshold_entry("a")))
            .and_then(|builder| builder.add_node(peer_gate("b")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("a").unwrap(),
                    NodeId::new("b").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![claim("alice", 0.4), claim("bob", 0.55), claim("carol", 0.9)];
        let deltas = [BinaryDelta {
            field: "strength".to_string(),
            delta: 0.2,
        }];

        let verdict = check_graph_monotonicity(&graph, &claims, &deltas).unwrap();

        assert!(matches!(verdict, Verdict::Rejected { .. }));
    }

    fn threshold_entry(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: vec![Gate::ThresholdGate {
                field: "strength".to_string(),
                min: 0.5,
                decision: Decision::Escalate,
            }],
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
        }
    }

    fn peer_gate(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: vec![Gate::PeerRelative {
                field: "strength".to_string(),
                percentile: 0.5,
                decision: Decision::Permit,
            }],
            default: Decision::Deny,
            combination: GateLogic::AnyMustPass,
        }
    }

    fn claim(claimant_id: &str, strength: f64) -> GovernanceClaim {
        GovernanceClaim {
            claimant_id: claimant_id.to_string(),
            strength,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        }
    }
}
