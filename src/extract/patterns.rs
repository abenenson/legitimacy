use super::pattern_support::{
    BranchSummary, SignalSummary, contains_any_phrase, decision_for_text, gate_decision,
    has_any_token_prefix, has_governance_keyword, has_policy_target_keyword,
    mentions_hook_registration, should_promote_literal, signal_summary,
};
use crate::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceGraph, GovernanceNode, GraphBuilder,
    LegitimacyError, NodeId,
    extract::{
        EdgeResolutionKind, ExtractionEvidenceTier, ExtractionReviewOverlay, ParsedFunction,
        RecognitionConfidence, RecognizedEdgeProvenance, RecognizedNodeProvenance, ResolutionIssue,
        ResolutionIssueKind,
    },
};
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, Debug)]
pub(crate) struct GraphBuildArtifacts {
    pub(crate) graph: GovernanceGraph,
    pub(crate) recognized_nodes: Vec<RecognizedNodeProvenance>,
    pub(crate) recognized_edges: Vec<RecognizedEdgeProvenance>,
    pub(crate) resolution_issues: Vec<ResolutionIssue>,
}

#[derive(Clone, Debug)]
pub(crate) struct RecognizedGovernanceFunction {
    pub(crate) id: String,
    pub(crate) function_name: String,
    pub(crate) qualified_symbol: String,
    pub(crate) relative_path: String,
    pub(crate) language: crate::extract::ExtractionSourceLanguage,
    pub(crate) line_start: usize,
    pub(crate) line_end: usize,
    pub(crate) confidence: RecognitionConfidence,
    pub(crate) rationale: Vec<String>,
    pub(crate) import_aliases: BTreeMap<String, String>,
    pub(crate) calls: BTreeSet<String>,
    pub(crate) callback_refs: BTreeSet<String>,
    pub(crate) node: GovernanceNode,
}

const DEFAULT_MIN_CONFIDENCE: RecognitionConfidence = RecognitionConfidence::Medium;

pub(crate) fn build_governance_graph_artifacts(
    parsed_functions: &[ParsedFunction],
    review_overlay: Option<&ExtractionReviewOverlay>,
) -> Result<GraphBuildArtifacts, LegitimacyError> {
    let recognized = parsed_functions
        .iter()
        .filter_map(recognize_governance_function)
        .collect::<Vec<_>>();

    if recognized.is_empty() {
        return Err(LegitimacyError::invalid_input(
            "no governance-relevant functions were discovered",
        ));
    }

    let mut builder = GraphBuilder::new()?;
    for function in &recognized {
        builder = builder.add_node(function.node.clone())?;
    }

    let mut by_name = HashMap::<String, Vec<&RecognizedGovernanceFunction>>::new();
    let mut by_qualified = HashMap::<String, &RecognizedGovernanceFunction>::new();
    let mut by_file_and_name = HashMap::<(String, String), &RecognizedGovernanceFunction>::new();
    for function in &recognized {
        by_name
            .entry(function.function_name.clone())
            .or_default()
            .push(function);
        by_qualified.insert(function.qualified_symbol.clone(), function);
        by_file_and_name.insert(
            (
                function.relative_path.clone(),
                function.function_name.clone(),
            ),
            function,
        );
    }

    let mut seen_edges = BTreeSet::new();
    let mut recognized_edges = Vec::new();
    let mut resolution_issues = Vec::new();
    for function in &recognized {
        for target in function.calls.iter().chain(function.callback_refs.iter()) {
            match resolve_target(target, function, &by_name, &by_qualified, &by_file_and_name) {
                ResolvedTarget::Resolved {
                    target: resolved,
                    resolution,
                } => {
                    if function.id != resolved.id
                        && seen_edges.insert((function.id.clone(), resolved.id.clone()))
                    {
                        builder = builder.add_edge(
                            NodeId::new(function.id.clone())?,
                            NodeId::new(resolved.id.clone())?,
                            EdgeTransform::PassThrough,
                        )?;
                        recognized_edges.push(RecognizedEdgeProvenance {
                            from: function.id.clone(),
                            to: resolved.id.clone(),
                            target_symbol: target.clone(),
                            resolution,
                            tier: ExtractionEvidenceTier::Automatic,
                            review_note: None,
                        });
                    }
                }
                ResolvedTarget::Unresolved => resolution_issues.push(ResolutionIssue {
                    caller: function.id.clone(),
                    target_symbol: target.clone(),
                    kind: ResolutionIssueKind::Unresolved,
                    candidates: Vec::new(),
                }),
                ResolvedTarget::Ambiguous { candidates } => {
                    resolution_issues.push(ResolutionIssue {
                        caller: function.id.clone(),
                        target_symbol: target.clone(),
                        kind: ResolutionIssueKind::Ambiguous,
                        candidates,
                    })
                }
            }
        }
    }

    apply_review_overlay(
        review_overlay,
        &recognized,
        &mut builder,
        &mut seen_edges,
        &mut recognized_edges,
        &mut resolution_issues,
    )?;

    let graph = builder.build()?;
    let recognized_nodes = recognized
        .iter()
        .map(|function| RecognizedNodeProvenance {
            node_id: function.id.clone(),
            function_name: function.function_name.clone(),
            relative_path: function.relative_path.clone(),
            language: function.language.clone(),
            line_start: function.line_start,
            line_end: function.line_end,
            confidence: function.confidence,
            tier: ExtractionEvidenceTier::Automatic,
            rationale: function.rationale.clone(),
        })
        .collect::<Vec<_>>();

    let mut recognized_nodes = recognized_nodes;
    if let Some(review_overlay) = review_overlay {
        for review in &review_overlay.reviewed_nodes {
            let node = recognized_nodes
                .iter_mut()
                .find(|node| node.node_id == review.node_id)
                .ok_or_else(|| {
                    LegitimacyError::invalid_input(format!(
                        "review overlay references unknown node '{}'",
                        review.node_id
                    ))
                })?;
            node.tier = ExtractionEvidenceTier::Reviewed;
            node.rationale
                .push(format!("reviewed overlay: {}", review.note));
        }
        for review in &review_overlay.reviewed_edges {
            let edge = recognized_edges
                .iter_mut()
                .find(|edge| {
                    edge.from == review.from
                        && edge.to == review.to
                        && review
                            .target_symbol
                            .as_ref()
                            .is_none_or(|target| target == &edge.target_symbol)
                })
                .ok_or_else(|| {
                    LegitimacyError::invalid_input(format!(
                        "review overlay references unknown edge '{} -> {}'",
                        review.from, review.to
                    ))
                })?;
            edge.tier = ExtractionEvidenceTier::Reviewed;
            edge.review_note = Some(review.note.clone());
        }
    }

    Ok(GraphBuildArtifacts {
        graph,
        recognized_nodes,
        recognized_edges,
        resolution_issues,
    })
}

fn recognize_governance_function(parsed: &ParsedFunction) -> Option<RecognizedGovernanceFunction> {
    if is_utility_helper(parsed) {
        return None;
    }

    let (confidence, rationale) = governance_confidence(parsed);
    if confidence < DEFAULT_MIN_CONFIDENCE {
        return None;
    }

    let mut gates = candidate_threshold_gates(parsed);
    gates.extend(candidate_match_gates(parsed));

    if mentions_hook_registration(parsed) {
        gates.push(Gate::ThresholdGate {
            field: "hook_registration".to_string(),
            min: 1.0,
            decision: Decision::Escalate,
        });
    }

    deduplicate_gates(&mut gates);

    if gates.is_empty() {
        return None;
    }

    let default = default_decision(&gates);
    let combination = combination_logic(parsed, &gates);
    let node = GovernanceNode::Binary {
        id: NodeId::new(parsed.id.clone()).ok()?,
        name: format!("{}:{}-{}", parsed.id, parsed.line_start, parsed.line_end),
        gates,
        default,
        combination,
    };

    Some(RecognizedGovernanceFunction {
        id: parsed.id.clone(),
        function_name: parsed.function_name.clone(),
        relative_path: parsed.relative_path.clone(),
        line_start: parsed.line_start,
        line_end: parsed.line_end,
        qualified_symbol: qualified_symbol_for(parsed),
        language: parsed.language.clone(),
        confidence,
        rationale,
        import_aliases: parsed.import_aliases.clone(),
        calls: parsed.calls.clone(),
        callback_refs: parsed.callback_refs.clone(),
        node,
    })
}

fn is_utility_helper(parsed: &ParsedFunction) -> bool {
    let function_name = parsed.function_name.as_str();
    function_name == "as_str"
        || function_name.starts_with("matcher_pattern_for_")
        || function_name.starts_with("validate_matcher_pattern")
        || function_name.starts_with("hook_run_for_")
}

fn governance_confidence(parsed: &ParsedFunction) -> (RecognitionConfidence, Vec<String>) {
    let mut rationale = Vec::new();
    if !has_governance_name_signal(parsed) {
        return (RecognitionConfidence::Low, rationale);
    }
    rationale.push("governance naming/path/body signal".to_string());

    if is_python_protocol_schema(parsed) {
        rationale.push("Python protocol schema surface".to_string());
        return (RecognitionConfidence::Medium, rationale);
    }

    let branch_summary = branch_summary(parsed);
    if branch_summary.total == 0 {
        return (RecognitionConfidence::Low, rationale);
    }
    rationale.push(format!(
        "branch structure with {} decision branches",
        branch_summary.total
    ));

    let output_signals = explicit_output_signals(parsed);
    let has_explicit_polarity = output_signals.positive > 0 || output_signals.negative > 0;
    if !has_explicit_polarity {
        return (RecognitionConfidence::Low, rationale);
    }
    rationale.push(format!(
        "explicit outputs positive={} negative={}",
        output_signals.positive, output_signals.negative
    ));

    let contextual_signals = contextual_signal_count(parsed);
    let language_signals = language_specific_signal_count(parsed);
    let has_balanced_branches = branch_summary.positive > 0 && branch_summary.negative > 0;
    let has_permission_context = branch_summary.contextual > 0
        || output_signals.contextual > 0
        || contextual_signals + language_signals >= 2;

    if has_balanced_branches && output_signals.positive > 0 && output_signals.negative > 0 {
        rationale.push("balanced permit/deny branch evidence".to_string());
        (RecognitionConfidence::High, rationale)
    } else if has_balanced_branches
        || has_permission_context
        || (branch_summary.total == 1 && has_explicit_polarity)
    {
        if has_balanced_branches {
            rationale.push("balanced branch polarity".to_string());
        }
        if has_permission_context {
            rationale.push("permission/policy context signal".to_string());
        }
        if language_signals > 0 {
            rationale.push(format!(
                "language-specific governance signals={language_signals}"
            ));
        }
        if branch_summary.total == 1 && has_explicit_polarity {
            rationale.push("single-branch gate with explicit polarity".to_string());
        }
        (RecognitionConfidence::Medium, rationale)
    } else {
        (RecognitionConfidence::Low, rationale)
    }
}

fn has_governance_name_signal(parsed: &ParsedFunction) -> bool {
    let function_name = parsed.function_name.to_ascii_lowercase();
    let relative_path = parsed.relative_path.to_ascii_lowercase();

    has_any_token_prefix(
        &function_name,
        &[
            "approval",
            "permission",
            "guard",
            "review",
            "hook",
            "sandbox",
            "policy",
        ],
    ) || has_any_token_prefix(
        &relative_path,
        &[
            "approval",
            "permission",
            "guard",
            "review",
            "hook",
            "sandbox",
            "policy",
        ],
    ) || contains_any_phrase(
        &parsed.body_text.to_ascii_lowercase(),
        &[
            "hookeventname",
            "permission_mode",
            "askforapproval",
            "sandboxpolicy",
            "should_block",
            "should_stop",
        ],
    )
}

fn branch_summary(parsed: &ParsedFunction) -> BranchSummary {
    let mut summary = BranchSummary::default();

    for branch in parsed
        .decision_branches
        .iter()
        .map(String::as_str)
        .chain(parsed.match_arms.iter().map(|arm| arm.body_text.as_str()))
    {
        let signals = signal_summary(branch);
        if signals.positive > 0 {
            summary.positive += 1;
        }
        if signals.negative > 0 {
            summary.negative += 1;
        }
        if signals.contextual > 0 {
            summary.contextual += 1;
        }
        summary.total += 1;
    }

    summary
}

fn explicit_output_signals(parsed: &ParsedFunction) -> SignalSummary {
    parsed
        .return_texts
        .iter()
        .chain(parsed.assignment_texts.iter())
        .fold(SignalSummary::default(), |mut summary, text| {
            let signals = signal_summary(text);
            summary.positive += signals.positive;
            summary.negative += signals.negative;
            summary.contextual += signals.contextual;
            summary
        })
}

fn contextual_signal_count(parsed: &ParsedFunction) -> usize {
    let mut signals = 0usize;

    if parsed
        .condition_fields
        .iter()
        .any(|field| has_governance_keyword(field))
    {
        signals += 1;
    }
    if parsed
        .condition_texts
        .iter()
        .any(|condition| has_governance_keyword(condition) || has_policy_target_keyword(condition))
    {
        signals += 1;
    }
    if parsed
        .string_literals
        .iter()
        .any(|literal| should_promote_literal(parsed, literal))
    {
        signals += 1;
    }
    if mentions_hook_registration(parsed) {
        signals += 1;
    }

    signals
}

fn language_specific_signal_count(parsed: &ParsedFunction) -> usize {
    match parsed.language {
        crate::extract::ExtractionSourceLanguage::Python => usize::from(
            parsed
                .calls
                .iter()
                .any(|call| has_any_token_prefix(call, &["require", "approve", "review"])),
        ),
        crate::extract::ExtractionSourceLanguage::Rust => usize::from(
            parsed
                .return_texts
                .iter()
                .chain(parsed.assignment_texts.iter())
                .any(|text| contains_any_phrase(text, &["Decision::", "PermissionMode::"])),
        ),
        crate::extract::ExtractionSourceLanguage::TypeScript => usize::from(
            parsed.body_text.contains("askForApproval")
                || parsed.body_text.contains("permissionMode")
                || parsed
                    .calls
                    .iter()
                    .any(|call| has_any_token_prefix(call, &["approve", "review", "register"])),
        ),
    }
}

fn is_python_protocol_schema(parsed: &ParsedFunction) -> bool {
    if parsed.language != crate::extract::ExtractionSourceLanguage::Python {
        return false;
    }

    let name = parsed.function_name.to_ascii_lowercase();
    let has_schema_name = name.contains("permission")
        || name.contains("hook")
        || name.contains("control")
        || name.contains("options");
    let has_schema_body = contains_any_phrase(
        &parsed.body_text.to_ascii_lowercase(),
        &[
            "literal[\"allow\"]",
            "literal[\"deny\"]",
            "literal[\"ask\"]",
            "literal[\"review\"]",
            "literal[\"defer\"]",
            "literal[\"escalate\"]",
            "literal[\"block\"]",
            "permissiondecision",
            "hookeventname",
            "can_use_tool",
            "permission_mode",
        ],
    );

    has_schema_name && has_schema_body
}

fn candidate_threshold_gates(parsed: &ParsedFunction) -> Vec<Gate> {
    parsed
        .condition_fields
        .iter()
        .filter(|field| has_governance_keyword(field))
        .filter_map(|field| {
            decision_for_text(field).map(|decision| Gate::ThresholdGate {
                field: field.to_string(),
                min: 1.0,
                decision,
            })
        })
        .take(8)
        .collect::<Vec<_>>()
}

fn candidate_match_gates(parsed: &ParsedFunction) -> Vec<Gate> {
    let condition_literals = parsed
        .condition_texts
        .iter()
        .flat_map(|condition| extract_condition_literals(condition))
        .collect::<Vec<_>>();
    let mut gates = parsed
        .match_arms
        .iter()
        .flat_map(|arm| {
            let arm_decision = decision_for_text(&arm.body_text)
                .or_else(|| decision_for_text(&arm.pattern_text))
                .unwrap_or(Decision::Escalate);

            arm.string_literals
                .iter()
                .filter(|literal| !literal.trim().is_empty())
                .filter(|literal| should_promote_literal(parsed, literal))
                .filter_map(|literal| classify_match_gate(literal, arm_decision.clone()))
                .collect::<Vec<_>>()
        })
        .take(8)
        .collect::<Vec<_>>();

    let literal_decision = parsed
        .return_texts
        .iter()
        .find_map(|return_text| decision_for_text(return_text))
        .or_else(|| decision_for_text(&parsed.body_text))
        .unwrap_or(Decision::Escalate);

    gates.extend(
        parsed
            .string_literals
            .iter()
            .chain(condition_literals.iter())
            .filter(|literal| should_promote_literal(parsed, literal))
            .filter_map(|literal| {
                let decision = python_literal_decision(parsed, literal)
                    .unwrap_or_else(|| literal_decision.clone());
                classify_match_gate(literal, decision)
            })
            .take(8),
    );

    gates.into_iter().take(8).collect()
}

fn python_literal_decision(parsed: &ParsedFunction, literal: &str) -> Option<Decision> {
    if !is_python_protocol_schema(parsed) {
        return None;
    }

    match literal.trim() {
        "allow" => Some(Decision::Permit),
        "deny" | "block" => Some(Decision::Deny),
        "ask" | "review" | "defer" | "escalate" => Some(Decision::Escalate),
        _ => decision_for_text(literal),
    }
}

fn extract_condition_literals(condition: &str) -> Vec<String> {
    let mut literals = Vec::new();
    let mut quote = None;
    let mut start = 0usize;

    for (index, character) in condition.char_indices() {
        match (quote, character) {
            (None, '"' | '\'') => {
                quote = Some(character);
                start = index + character.len_utf8();
            }
            (Some(open), current) if current == open => {
                if start <= index {
                    let literal = condition[start..index].trim();
                    if !literal.is_empty() {
                        literals.push(literal.to_string());
                    }
                }
                quote = None;
            }
            _ => {}
        }
    }

    literals
}

fn classify_match_gate(literal: &str, decision: Decision) -> Option<Gate> {
    let trimmed = literal.trim();
    if trimmed.is_empty() {
        return None;
    }

    if trimmed.starts_with('/')
        || trimmed.contains(std::path::MAIN_SEPARATOR)
        || trimmed.contains(".rs")
        || trimmed.contains(".toml")
    {
        return Some(Gate::PrefixMatch {
            pattern: trimmed.to_string(),
            decision,
        });
    }

    if looks_like_glob_or_regex(trimmed) {
        return Some(Gate::ContentMatch {
            regex: trimmed.to_string(),
            decision,
        });
    }

    if trimmed.contains(' ')
        || trimmed.contains('\t')
        || trimmed.contains("&&")
        || trimmed.contains("||")
        || trimmed.contains(';')
    {
        return Some(Gate::ContentMatch {
            regex: regex::escape(trimmed),
            decision,
        });
    }

    if trimmed.chars().all(|character| {
        character.is_ascii_alphanumeric() || matches!(character, '_' | '-' | ':' | '.')
    }) {
        return Some(Gate::ExactMatch {
            value: trimmed.to_string(),
            decision,
        });
    }

    Some(Gate::ContentMatch {
        regex: regex::escape(trimmed),
        decision,
    })
}

fn looks_like_glob_or_regex(literal: &str) -> bool {
    literal
        .chars()
        .all(|character| !character.is_whitespace() && character.is_ascii())
        && literal.contains("mcp__")
        && (literal.contains(".*") || literal.ends_with('*'))
}

fn deduplicate_gates(gates: &mut Vec<Gate>) {
    let mut seen = BTreeSet::new();
    gates.retain(|gate| match gate {
        Gate::PrefixMatch { pattern, decision } => {
            seen.insert(format!("prefix:{pattern}:{decision:?}"))
        }
        Gate::ExactMatch { value, decision } => seen.insert(format!("exact:{value}:{decision:?}")),
        Gate::ContentMatch { regex, decision } => {
            seen.insert(format!("content:{regex}:{decision:?}"))
        }
        Gate::ThresholdGate {
            field,
            min,
            decision,
        } => seen.insert(format!("threshold:{field}:{min}:{decision:?}")),
        Gate::PeerRelative {
            field,
            percentile,
            decision,
        } => seen.insert(format!("peer:{field}:{percentile}:{decision:?}")),
    });
}

fn default_decision(gates: &[Gate]) -> Decision {
    let has_permit = gates
        .iter()
        .any(|gate| gate_decision(gate) == &Decision::Permit);
    let has_deny = gates
        .iter()
        .any(|gate| gate_decision(gate) == &Decision::Deny);
    let has_escalate = gates
        .iter()
        .any(|gate| gate_decision(gate) == &Decision::Escalate);

    match (has_permit, has_deny, has_escalate) {
        (false, true, _) => Decision::Permit,
        (true, false, false) => Decision::Deny,
        (_, _, true) => Decision::Permit,
        _ => Decision::Escalate,
    }
}

fn combination_logic(parsed: &ParsedFunction, gates: &[Gate]) -> GateLogic {
    if parsed.has_if_chain || !parsed.match_arms.is_empty() {
        GateLogic::FirstMatch
    } else if gates.len() > 1
        && (parsed.body_text.contains("&&") || parsed.body_text.contains(".all("))
    {
        GateLogic::AllMustPass
    } else if gates.len() > 1
        && (parsed.body_text.contains("||") || parsed.body_text.contains(".any("))
    {
        GateLogic::AnyMustPass
    } else {
        GateLogic::FirstMatch
    }
}

fn qualified_symbol_for(parsed: &ParsedFunction) -> String {
    let mut path = parsed.relative_path.replace('\\', "/");
    if let Some(stripped) = path.strip_suffix(".rs") {
        path = stripped.to_string();
    } else if let Some(stripped) = path.strip_suffix(".py") {
        path = stripped.replace('/', ".");
    } else if let Some(stripped) = path.strip_suffix(".tsx") {
        path = stripped.replace('/', ".");
    } else if let Some(stripped) = path.strip_suffix(".ts") {
        path = stripped.replace('/', ".");
    }

    match parsed.language {
        crate::extract::ExtractionSourceLanguage::Rust => {
            format!("{}::{}", path.replace('/', "::"), parsed.function_name)
        }
        crate::extract::ExtractionSourceLanguage::Python
        | crate::extract::ExtractionSourceLanguage::TypeScript => {
            format!("{}.{}", path, parsed.function_name)
        }
    }
}

enum ResolvedTarget<'a> {
    Resolved {
        target: &'a RecognizedGovernanceFunction,
        resolution: EdgeResolutionKind,
    },
    Unresolved,
    Ambiguous {
        candidates: Vec<String>,
    },
}

fn resolve_target<'a>(
    target: &str,
    caller: &RecognizedGovernanceFunction,
    by_name: &'a HashMap<String, Vec<&'a RecognizedGovernanceFunction>>,
    by_qualified: &'a HashMap<String, &'a RecognizedGovernanceFunction>,
    by_file_and_name: &'a HashMap<(String, String), &'a RecognizedGovernanceFunction>,
) -> ResolvedTarget<'a> {
    if let Some(found) = by_file_and_name.get(&(caller.relative_path.clone(), target.to_string())) {
        return ResolvedTarget::Resolved {
            target: found,
            resolution: EdgeResolutionKind::SameFile,
        };
    }

    if let Some(import_target) = caller.import_aliases.get(target)
        && let Some(found) = by_qualified.get(import_target)
    {
        return ResolvedTarget::Resolved {
            target: found,
            resolution: EdgeResolutionKind::ImportAlias,
        };
    }

    if let Some(found) = by_qualified.get(target) {
        return ResolvedTarget::Resolved {
            target: found,
            resolution: EdgeResolutionKind::ImportAlias,
        };
    }

    match by_name.get(target) {
        Some(candidates) if candidates.len() == 1 => ResolvedTarget::Resolved {
            target: candidates[0],
            resolution: EdgeResolutionKind::GlobalUnique,
        },
        Some(candidates) if !candidates.is_empty() => ResolvedTarget::Ambiguous {
            candidates: candidates
                .iter()
                .map(|candidate| candidate.id.clone())
                .collect(),
        },
        _ => ResolvedTarget::Unresolved,
    }
}

fn apply_review_overlay(
    review_overlay: Option<&ExtractionReviewOverlay>,
    recognized: &[RecognizedGovernanceFunction],
    builder: &mut GraphBuilder,
    seen_edges: &mut BTreeSet<(String, String)>,
    recognized_edges: &mut Vec<RecognizedEdgeProvenance>,
    resolution_issues: &mut Vec<ResolutionIssue>,
) -> Result<(), LegitimacyError> {
    let Some(review_overlay) = review_overlay else {
        return Ok(());
    };

    let recognized_by_id = recognized
        .iter()
        .map(|function| (function.id.as_str(), function))
        .collect::<HashMap<_, _>>();

    for alias in &review_overlay.alias_hints {
        let caller = recognized_by_id.get(alias.caller.as_str()).ok_or_else(|| {
            LegitimacyError::invalid_input(format!(
                "review overlay references unknown caller '{}'",
                alias.caller
            ))
        })?;
        let callee = recognized_by_id.get(alias.callee.as_str()).ok_or_else(|| {
            LegitimacyError::invalid_input(format!(
                "review overlay references unknown callee '{}'",
                alias.callee
            ))
        })?;

        if seen_edges.insert((caller.id.clone(), callee.id.clone())) {
            *builder = builder.clone().add_edge(
                NodeId::new(caller.id.clone())?,
                NodeId::new(callee.id.clone())?,
                EdgeTransform::PassThrough,
            )?;
            recognized_edges.push(RecognizedEdgeProvenance {
                from: caller.id.clone(),
                to: callee.id.clone(),
                target_symbol: alias.target_symbol.clone(),
                resolution: EdgeResolutionKind::ReviewOverlay,
                tier: ExtractionEvidenceTier::Reviewed,
                review_note: Some(alias.note.clone()),
            });
        } else if let Some(edge) = recognized_edges
            .iter_mut()
            .find(|edge| edge.from == caller.id && edge.to == callee.id)
        {
            edge.tier = ExtractionEvidenceTier::Reviewed;
            edge.review_note = Some(alias.note.clone());
        }

        resolution_issues.retain(|issue| {
            !(issue.caller == alias.caller && issue.target_symbol == alias.target_symbol)
        });
    }

    Ok(())
}
