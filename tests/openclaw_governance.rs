use std::{
    collections::BTreeMap,
    fmt, fs,
    path::{Path, PathBuf},
};

use legitimacy::{
    Decision, EdgeTransform, GovernanceClaim, GovernanceGraph, GovernanceNode, GraphBuilder,
    NodeId, Verdict,
    axioms::graph::{consistency::check_graph_consistency, monotonicity::check_graph_monotonicity},
    graph::{Gate, GateLogic},
    traverse,
};

const OPENCLAW_ROOT: &str = "audits/fixtures/sources/leaderboard/openclaw-infra";
const OPENCLAW_AGENTS_ROOT: &str = "audits/fixtures/sources/leaderboard/openclaw-agents";

fn openclaw_fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(OPENCLAW_ROOT)
}

fn openclaw_agents_fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(OPENCLAW_AGENTS_ROOT)
}

#[derive(Clone, Debug)]
struct SourceSpan {
    relative_path: &'static str,
    start_line: usize,
    end_line: usize,
}

impl fmt::Display for SourceSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.start_line == self.end_line {
            write!(f, "{}#L{}", self.relative_path, self.start_line)
        } else {
            write!(
                f,
                "{}#L{}-L{}",
                self.relative_path, self.start_line, self.end_line
            )
        }
    }
}

#[test]
fn openclaw_allowlist_skill_prelude_breaks_consistency() {
    let graph = openclaw_allowlist_graph();
    let before = final_decisions(&graph, &allowlist_claims_with_trusted_skill());
    let after = final_decisions(&graph, &allowlist_claims_without_trusted_skill());
    let source_trace = join_spans(&allowlist_consistency_spans());

    println!(
        "OpenClaw allowlist consistency witness: skill prelude changed after trusted execution removal; source trace: {}",
        source_trace
    );

    assert_eq!(before["skill-prelude"], Decision::Permit);
    assert_eq!(after["skill-prelude"], Decision::Deny);
    assert_eq!(before["plain-allowlisted"], Decision::Permit);
    assert_eq!(after["plain-allowlisted"], Decision::Permit);
}

#[test]
fn openclaw_failover_policy_breaks_solidarity() {
    let graph = openclaw_failover_graph();
    let before = final_decisions(&graph, &failover_claims_before_provider_failure());
    let after = final_decisions(&graph, &failover_claims_after_model_not_found_probe());
    let source_trace = join_spans(&failover_solidarity_spans());

    println!(
        "OpenClaw failover solidarity witness: preserved transient probe slot made one same-tier model better and another worse; source trace: {}",
        source_trace
    );

    assert_eq!(before["anthropic-sonnet"], Decision::Permit);
    assert_eq!(after["anthropic-sonnet"], Decision::Deny);
    assert_eq!(before["anthropic-haiku"], Decision::Deny);
    assert_eq!(after["anthropic-haiku"], Decision::Permit);
}

#[test]
fn openclaw_exec_pipeline_stays_monotone_in_approval_evidence() {
    let graph = openclaw_exec_pipeline_graph();
    let claims = monotone_pipeline_claims();
    let deltas = vec![
        legitimacy::axioms::binary::BinaryDelta {
            field: "analysis_ok".to_string(),
            delta: 1.0,
        },
        legitimacy::axioms::binary::BinaryDelta {
            field: "allowlist_match".to_string(),
            delta: 1.0,
        },
        legitimacy::axioms::binary::BinaryDelta {
            field: "durable_trust".to_string(),
            delta: 1.0,
        },
    ];
    let verdict = check_graph_monotonicity(&graph, &claims, &deltas).unwrap();

    println!(
        "OpenClaw monotonicity check source trace: {}",
        join_spans(&monotonicity_pass_spans())
    );

    assert!(
        matches!(verdict, Verdict::Admissible { .. }),
        "stronger exec-approval evidence should not worsen any tool: {verdict:?}"
    );
}

#[test]
fn openclaw_allow_always_append_is_not_alabama_paradoxical_for_existing_tools() {
    let graph = openclaw_exec_pipeline_graph();
    let before_claims = existing_allow_always_claims();
    let after_claims = claims_with_added_allow_always_tool();
    let before = final_decisions(&graph, &before_claims);
    let after = final_decisions(&graph, &after_claims);
    let consistency = check_graph_consistency(&graph, &after_claims).unwrap();

    println!(
        "OpenClaw allow-always append check source trace: {}",
        join_spans(&allow_always_append_spans())
    );

    assert_eq!(before["existing-durable"], after["existing-durable"]);
    assert_eq!(before["existing-on-miss"], after["existing-on-miss"]);
    assert!(
        matches!(consistency, Verdict::Admissible { .. }),
        "adding a disjoint allow-always entry should not change survivors under reverse removal: {consistency:?}"
    );
}

fn openclaw_allowlist_graph() -> GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("allowlist").unwrap(),
                name: "allowlist".to_string(),
                gates: vec![
                    Gate::ExactMatch {
                        value: "trusted-skill-exec".to_string(),
                        decision: Decision::Permit,
                    },
                    Gate::ExactMatch {
                        value: "skill-prelude-reachable".to_string(),
                        decision: Decision::Permit,
                    },
                    Gate::ExactMatch {
                        value: "plain-allowlisted".to_string(),
                        decision: Decision::Permit,
                    },
                ],
                default: Decision::Deny,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn openclaw_failover_graph() -> GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("failover-surface").unwrap(),
                name: "failover-surface".to_string(),
                gates: vec![
                    Gate::ExactMatch {
                        value: "primary-open".to_string(),
                        decision: Decision::Permit,
                    },
                    Gate::ExactMatch {
                        value: "later-same-provider-probe-open".to_string(),
                        decision: Decision::Permit,
                    },
                ],
                default: Decision::Deny,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn openclaw_exec_pipeline_graph() -> GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("analysis").unwrap(),
                name: "analysis".to_string(),
                gates: vec![Gate::ThresholdGate {
                    field: "analysis_ok".to_string(),
                    min: 1.0,
                    decision: Decision::Escalate,
                }],
                default: Decision::Deny,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("effective-policy").unwrap(),
                name: "effective-policy".to_string(),
                gates: vec![Gate::ThresholdGate {
                    field: "security_allowlist".to_string(),
                    min: 1.0,
                    decision: Decision::Escalate,
                }],
                default: Decision::Permit,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("surface").unwrap(),
                name: "surface".to_string(),
                gates: vec![
                    Gate::ThresholdGate {
                        field: "durable_trust".to_string(),
                        min: 1.0,
                        decision: Decision::Permit,
                    },
                    Gate::ThresholdGate {
                        field: "allowlist_match".to_string(),
                        min: 1.0,
                        decision: Decision::Permit,
                    },
                ],
                default: Decision::Escalate,
                combination: GateLogic::AnyMustPass,
            })
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("analysis").unwrap(),
                NodeId::new("effective-policy").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("effective-policy").unwrap(),
                NodeId::new("surface").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn allowlist_claims_with_trusted_skill() -> Vec<GovernanceClaim> {
    vec![
        claim(
            "skill-prelude",
            "skill-prelude-reachable",
            "skill-chain",
            metrics([]),
        ),
        claim(
            "trusted-wrapper",
            "trusted-skill-exec",
            "skill-chain",
            metrics([]),
        ),
        claim(
            "plain-allowlisted",
            "plain-allowlisted",
            "control",
            metrics([]),
        ),
    ]
}

fn allowlist_claims_without_trusted_skill() -> Vec<GovernanceClaim> {
    vec![
        claim(
            "skill-prelude",
            "skill-prelude-unreachable",
            "skill-chain",
            metrics([]),
        ),
        claim(
            "plain-allowlisted",
            "plain-allowlisted",
            "control",
            metrics([]),
        ),
    ]
}

fn failover_claims_before_provider_failure() -> Vec<GovernanceClaim> {
    vec![
        claim(
            "anthropic-sonnet",
            "primary-open",
            "provider-tier:anthropic",
            metrics([]),
        ),
        claim(
            "anthropic-haiku",
            "later-same-provider-standby",
            "provider-tier:anthropic",
            metrics([]),
        ),
    ]
}

fn failover_claims_after_model_not_found_probe() -> Vec<GovernanceClaim> {
    vec![
        claim(
            "anthropic-sonnet",
            "primary-failed-model-not-found",
            "provider-tier:anthropic",
            metrics([]),
        ),
        claim(
            "anthropic-haiku",
            "later-same-provider-probe-open",
            "provider-tier:anthropic",
            metrics([]),
        ),
    ]
}

fn monotone_pipeline_claims() -> Vec<GovernanceClaim> {
    vec![
        claim(
            "parse-failure",
            "exec",
            "exec-tools",
            metrics([
                ("analysis_ok", 0.0),
                ("security_allowlist", 1.0),
                ("allowlist_match", 0.0),
                ("durable_trust", 0.0),
            ]),
        ),
        claim(
            "needs-approval",
            "exec",
            "exec-tools",
            metrics([
                ("analysis_ok", 1.0),
                ("security_allowlist", 1.0),
                ("allowlist_match", 0.0),
                ("durable_trust", 0.0),
            ]),
        ),
        claim(
            "allowlist-hit",
            "exec",
            "exec-tools",
            metrics([
                ("analysis_ok", 1.0),
                ("security_allowlist", 1.0),
                ("allowlist_match", 1.0),
                ("durable_trust", 0.0),
            ]),
        ),
        claim(
            "durable-hit",
            "exec",
            "exec-tools",
            metrics([
                ("analysis_ok", 1.0),
                ("security_allowlist", 1.0),
                ("allowlist_match", 0.0),
                ("durable_trust", 1.0),
            ]),
        ),
    ]
}

fn existing_allow_always_claims() -> Vec<GovernanceClaim> {
    vec![
        claim(
            "existing-durable",
            "exec",
            "exec-tools",
            metrics([
                ("analysis_ok", 1.0),
                ("security_allowlist", 1.0),
                ("allowlist_match", 0.0),
                ("durable_trust", 1.0),
            ]),
        ),
        claim(
            "existing-on-miss",
            "exec",
            "exec-tools",
            metrics([
                ("analysis_ok", 1.0),
                ("security_allowlist", 1.0),
                ("allowlist_match", 0.0),
                ("durable_trust", 0.0),
            ]),
        ),
    ]
}

fn claims_with_added_allow_always_tool() -> Vec<GovernanceClaim> {
    let mut claims = existing_allow_always_claims();
    claims.push(claim(
        "new-durable-tool",
        "exec",
        "exec-tools",
        metrics([
            ("analysis_ok", 1.0),
            ("security_allowlist", 1.0),
            ("allowlist_match", 0.0),
            ("durable_trust", 1.0),
        ]),
    ));
    claims
}

fn claim(
    claimant_id: &str,
    action: &str,
    priority_class: &str,
    metrics: BTreeMap<String, f64>,
) -> GovernanceClaim {
    GovernanceClaim {
        claimant_id: claimant_id.to_string(),
        strength: 1.0,
        priority_class: Some(priority_class.to_string()),
        path: None,
        action: Some(action.to_string()),
        content: None,
        metrics,
    }
}

fn metrics<const N: usize>(entries: [(&str, f64); N]) -> BTreeMap<String, f64> {
    entries
        .into_iter()
        .map(|(key, value)| (key.to_string(), value))
        .collect()
}

fn final_decisions(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> BTreeMap<String, Decision> {
    traverse(graph, claims).unwrap().final_decisions
}

fn allowlist_consistency_spans() -> Vec<(&'static str, SourceSpan)> {
    vec![
        (
            "prelude classifier",
            span_for(
                "src/infra/exec-approvals-allowlist.ts",
                "function isSkillPreludeOnlyEvaluation(",
                "return segments.length > 0 && segments.every((segment) => isSkillPreludeSegment(segment, cwd));",
            ),
        ),
        (
            "trusted skill extraction",
            span_for(
                "src/infra/exec-approvals-allowlist.ts",
                "for (const [index, segment] of params.analysis.segments.entries()) {",
                "return skillIds;",
            ),
        ),
        (
            "backward reachability",
            span_for(
                "src/infra/exec-approvals-allowlist.ts",
                "for (let index = finalizedEvaluations.length - 1; index >= 0; index -= 1) {",
                "allowSkillPreludeAtIndex.add(index);",
            ),
        ),
    ]
}

fn failover_solidarity_spans() -> Vec<(&'static str, SourceSpan)> {
    vec![
        (
            "transient slot policy",
            span_for(
                "src/agents/failover-policy.ts",
                "export function shouldUseTransientCooldownProbeSlot(",
                "reason === \"timeout\"",
            ),
        ),
        (
            "one probe per provider",
            span_for(
                "src/agents/model-fallback.ts",
                "if (shouldAllowCooldownProbeForReason(decision.reason)) {",
                "transientProbeProviderForAttempt = candidate.provider;",
            ),
        ),
        (
            "slot preservation",
            span_for(
                "src/agents/model-fallback.ts",
                "if (!shouldPreserveTransientCooldownProbeSlot(probeFailureReason)) {",
                "cooldownProbeUsedProviders.add(transientProbeProviderForAttempt);",
            ),
        ),
        (
            "model_not_found witness",
            span_for(
                "src/agents/model-fallback.test.ts",
                "it(\"does not consume transient probe slot when first same-provider probe fails with model_not_found\", async () => {",
                "allowTransientCooldownProbe: true,",
            ),
        ),
    ]
}

fn monotonicity_pass_spans() -> Vec<(&'static str, SourceSpan)> {
    vec![
        (
            "requires approval",
            span_for(
                "src/infra/exec-approvals.ts",
                "export function requiresExecApproval(params: {",
                "(!params.analysisOk || !params.allowlistSatisfied)",
            ),
        ),
        (
            "durable trust",
            span_for(
                "src/infra/exec-approvals.ts",
                "export function hasDurableExecApproval(params: {",
                "params.segmentAllowlistEntries.every((entry) => entry?.source === \"allow-always\")",
            ),
        ),
        (
            "effective merge",
            span_for(
                "src/infra/exec-approvals-effective.ts",
                "const effectiveSecurity = minSecurity(requestedSecurity.value, resolved.agent.security);",
                "allowedDecisions: resolveExecApprovalAllowedDecisions({ ask: effectiveAsk }),",
            ),
        ),
    ]
}

fn allow_always_append_spans() -> Vec<(&'static str, SourceSpan)> {
    vec![
        (
            "allow-always derivation",
            span_for(
                "src/infra/exec-approvals-allowlist.ts",
                "export function resolveAllowAlwaysPatternEntries(params: {",
                "return patterns;",
            ),
        ),
        (
            "allow-always persistence",
            span_for(
                "src/infra/exec-approvals.ts",
                "export function persistAllowAlwaysPatterns(params: {",
                "return patterns;",
            ),
        ),
        (
            "allowlist append",
            span_for(
                "src/infra/exec-approvals.ts",
                "export function addAllowlistEntry(",
                "saveExecApprovals(approvals);",
            ),
        ),
    ]
}

fn join_spans(spans: &[(&'static str, SourceSpan)]) -> String {
    spans
        .iter()
        .map(|(label, span)| format!("{label}: {span}"))
        .collect::<Vec<_>>()
        .join("; ")
}

fn span_for(relative_path: &'static str, start: &str, end: &str) -> SourceSpan {
    SourceSpan {
        relative_path,
        start_line: line_for(relative_path, start),
        end_line: line_for_after(relative_path, start, end),
    }
}

fn line_for(relative_path: &'static str, needle: &str) -> usize {
    let full_path = fixture_path_for(relative_path);
    let contents = fs::read_to_string(&full_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", full_path.display()));

    contents
        .lines()
        .position(|line| line.contains(needle))
        .map(|index| index + 1)
        .unwrap_or_else(|| panic!("failed to find {:?} in {}", needle, full_path.display()))
}

fn line_for_after(relative_path: &'static str, start: &str, needle: &str) -> usize {
    let full_path = fixture_path_for(relative_path);
    let contents = fs::read_to_string(&full_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", full_path.display()));
    let lines = contents.lines().collect::<Vec<_>>();
    let start_index = lines
        .iter()
        .position(|line| line.contains(start))
        .unwrap_or_else(|| panic!("failed to find {:?} in {}", start, full_path.display()));

    lines
        .iter()
        .enumerate()
        .skip(start_index)
        .find_map(|(index, line)| line.contains(needle).then_some(index + 1))
        .unwrap_or_else(|| {
            panic!(
                "failed to find {:?} after {:?} in {}",
                needle,
                start,
                full_path.display()
            )
        })
}

fn fixture_path_for(relative_path: &'static str) -> PathBuf {
    if let Some(normalized) = relative_path.strip_prefix("src/infra/") {
        return openclaw_fixture_root().join(normalized);
    }
    if let Some(normalized) = relative_path.strip_prefix("src/agents/") {
        return openclaw_agents_fixture_root().join(normalized);
    }
    openclaw_fixture_root().join(relative_path)
}
