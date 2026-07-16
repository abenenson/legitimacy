use super::{
    ExtractionCoverageReport, ExtractionEvidenceTier, ExtractionFileReport, ExtractionFileStatus,
    ExtractionOptions, ExtractionSourceLanguage, GovernanceExtractionArtifacts,
    RecognitionConfidence, RecognizedEdgeProvenance, RecognizedNodeProvenance, SourceLanguage,
    collect_source_files,
    typescript_approval_core_parser::{
        TypeScriptApprovalCoreApprovalResult, TypeScriptApprovalCoreAst,
        TypeScriptApprovalCoreHandler, TypeScriptApprovalCorePolicyKind,
        TypeScriptApprovalCoreRegistration, TypeScriptApprovalCoreSourceSpan,
        approval_result_from_literal, approval_result_literal, parse_typescript_approval_core,
    },
};
use crate::{
    BoundaryCausalSafetyAssessment, Decision, EdgeTransform, Gate, GateLogic, GovernanceGraph,
    GovernanceNode, GraphBuilder, LegitimacyError, NodeId,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

const EXTRACTION_THEOREM: &str = "extractTypeScriptApprovalCore_decision_equivalent";
const FAILURE_THEOREM: &str =
    "typescript_approval_modeled_program_extractor_failure_reflects_modeled_source_failure";

pub(crate) fn extract_typescript_approval_core_artifacts(
    source_dir: &Path,
    options: ExtractionOptions,
) -> Result<GovernanceExtractionArtifacts, LegitimacyError> {
    let source_files = collect_source_files(source_dir)?;
    if source_files.is_empty() {
        return Err(LegitimacyError::invalid_input(format!(
            "no supported source files were discovered under '{}'",
            source_dir.display()
        )));
    }
    if source_files
        .iter()
        .any(|(_, language)| *language != SourceLanguage::TypeScript)
    {
        return Err(LegitimacyError::invalid_input(
            "theorem-backed TypeScriptApprovalCore mode accepts TypeScript source files only",
        ));
    }
    if options.allow_partial {
        return Err(LegitimacyError::invalid_input(
            "theorem-backed TypeScriptApprovalCore mode refuses unsupported constructs instead of partial extraction",
        ));
    }

    let mut reports = Vec::new();
    let mut files = Vec::new();
    for (path, _) in source_files {
        let source = fs::read_to_string(&path).map_err(|source| LegitimacyError::Io {
            context: format!("TypeScriptApprovalCore source '{}'", path.display()),
            source,
        })?;
        let relative_path = path
            .strip_prefix(source_dir)
            .unwrap_or(path.as_path())
            .to_string_lossy()
            .replace('\\', "/");
        match parse_typescript_approval_core(&source) {
            Ok(ast) => {
                reports.push(ExtractionFileReport {
                    path: relative_path.clone(),
                    language: ExtractionSourceLanguage::TypeScript,
                    status: ExtractionFileStatus::Parsed,
                    detail: Some(format!("TypeScriptApprovalCore AST {}", ast.canonical_hash)),
                });
                files.push(TypeScriptApprovalCoreFile {
                    path: relative_path,
                    ast,
                });
            }
            Err(error) => {
                reports.push(ExtractionFileReport {
                    path: relative_path,
                    language: ExtractionSourceLanguage::TypeScript,
                    status: ExtractionFileStatus::Error,
                    detail: Some(error.to_string()),
                });
                return Err(LegitimacyError::invalid_input(format!(
                    "UnsupportedConstruct: {error}"
                )));
            }
        }
    }

    let build = build_graph(files)?;
    Ok(GovernanceExtractionArtifacts {
        source_dir: source_dir.display().to_string(),
        graph: build.graph,
        coverage: ExtractionCoverageReport::from_files(reports),
        recognized_nodes: build.nodes,
        recognized_edges: build.edges,
        resolution_issues: build.resolution_issues,
        review_overlay: None,
        boundary_causal_safety: BoundaryCausalSafetyAssessment::default(),
    })
}

struct CoreGraphBuild {
    graph: GovernanceGraph,
    nodes: Vec<RecognizedNodeProvenance>,
    edges: Vec<RecognizedEdgeProvenance>,
    resolution_issues: Vec<super::ResolutionIssue>,
}

struct TypeScriptApprovalCoreFile {
    path: String,
    ast: TypeScriptApprovalCoreAst,
}

#[derive(Clone, Copy)]
struct HandlerLocation {
    file_index: usize,
    handler_index: usize,
}

fn build_graph(files: Vec<TypeScriptApprovalCoreFile>) -> Result<CoreGraphBuild, LegitimacyError> {
    let mut builder = GraphBuilder::new()?;
    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut resolution_issues = Vec::new();
    let mut seen_nodes = BTreeSet::new();
    let mut handler_index: BTreeMap<String, Vec<HandlerLocation>> = BTreeMap::new();

    for (file_index, file) in files.iter().enumerate() {
        for (handler_index_in_file, handler) in file.ast.handlers.iter().enumerate() {
            handler_index
                .entry(handler.name.clone())
                .or_default()
                .push(HandlerLocation {
                    file_index,
                    handler_index: handler_index_in_file,
                });
        }
    }

    for file in &files {
        let path = &file.path;
        let ast = &file.ast;
        for union in &ast.approval_unions {
            let gates = union_decision_gates(&union.literals);
            if !gates.is_empty() {
                let id = format!("{path}::{}", union.name);
                add_node_once(
                    &mut builder,
                    &mut nodes,
                    &mut seen_nodes,
                    binary_node(&id, gates, Decision::Escalate)?,
                    recognized_node(&id, &union.name, path, ast, Some(&union.span)),
                )?;
            }
        }
        for policy in &ast.policies {
            let id = format!("{path}::{}", policy.name);
            let decision = match policy.kind {
                TypeScriptApprovalCorePolicyKind::Allowlist => Decision::Permit,
                TypeScriptApprovalCorePolicyKind::Blocklist => Decision::Deny,
            };
            let default = match policy.kind {
                TypeScriptApprovalCorePolicyKind::Allowlist => Decision::Escalate,
                TypeScriptApprovalCorePolicyKind::Blocklist => Decision::Permit,
            };
            let gates = policy
                .entries
                .iter()
                .map(|entry| Gate::ExactMatch {
                    value: entry.clone(),
                    decision: decision.clone(),
                })
                .collect::<Vec<_>>();
            add_node_once(
                &mut builder,
                &mut nodes,
                &mut seen_nodes,
                binary_node(&id, gates, default)?,
                recognized_node(&id, &policy.name, path, ast, Some(&policy.span)),
            )?;
        }
    }

    let mut registered_handlers = BTreeSet::new();
    for (file_index, file) in files.iter().enumerate() {
        for registration in &file.ast.registrations {
            let registration_id = registration_node_id(&file.path, registration);
            let Some(location) = resolve_handler(
                &files,
                &handler_index,
                &file.path,
                registration,
                &registration_id,
                &mut resolution_issues,
            ) else {
                continue;
            };
            let handler_id = handler_id(&files, location);
            add_node_once(
                &mut builder,
                &mut nodes,
                &mut seen_nodes,
                binary_node(
                    &registration_id,
                    vec![Gate::ThresholdGate {
                        field: format!("approval_registration:{}", registration.surface),
                        min: 1.0,
                        decision: Decision::Escalate,
                    }],
                    Decision::Permit,
                )?,
                recognized_node(
                    &registration_id,
                    "approval registration",
                    &file.path,
                    &file.ast,
                    Some(&registration.span),
                ),
            )?;
            add_handler_node(&files, location, &mut builder, &mut nodes, &mut seen_nodes)?;
            registered_handlers.insert(handler_id.clone());
            builder = builder.add_edge(
                NodeId::new(registration_id.clone())?,
                NodeId::new(handler_id.clone())?,
                EdgeTransform::PassThrough,
            )?;
            edges.push(RecognizedEdgeProvenance {
                from: registration_id,
                to: handler_id,
                target_symbol: registration.handler.clone(),
                resolution: super::EdgeResolutionKind::SameFile,
                tier: ExtractionEvidenceTier::Automatic,
                review_note: None,
            });
        }
        for (handler_index_in_file, handler) in file.ast.handlers.iter().enumerate() {
            if file.ast.registrations.is_empty() && handler.name.starts_with("should") {
                let location = HandlerLocation {
                    file_index,
                    handler_index: handler_index_in_file,
                };
                add_handler_node(&files, location, &mut builder, &mut nodes, &mut seen_nodes)?;
            }
        }
    }

    for file in &files {
        for handler in &file.ast.handlers {
            let from = format!("{}::{}", file.path, handler.name);
            if !registered_handlers.contains(&from) && !from.contains("should") {
                continue;
            }
            for call in &handler.calls {
                let Some(locations) = handler_index.get(call) else {
                    continue;
                };
                let to = handler_id(&files, locations[0]);
                if from == to {
                    continue;
                }
                builder = builder.add_edge(
                    NodeId::new(from.clone())?,
                    NodeId::new(to.clone())?,
                    EdgeTransform::PassThrough,
                )?;
                edges.push(RecognizedEdgeProvenance {
                    from: from.clone(),
                    to,
                    target_symbol: call.clone(),
                    resolution: super::EdgeResolutionKind::GlobalUnique,
                    tier: ExtractionEvidenceTier::Automatic,
                    review_note: None,
                });
            }
        }
    }

    if nodes.is_empty() {
        return Err(LegitimacyError::invalid_input(
            "no TypeScriptApprovalCore approval union, policy, handler, or registration was discovered",
        ));
    }

    Ok(CoreGraphBuild {
        graph: builder.build()?,
        nodes,
        edges,
        resolution_issues,
    })
}

fn add_handler_node(
    files: &[TypeScriptApprovalCoreFile],
    location: HandlerLocation,
    builder: &mut GraphBuilder,
    nodes: &mut Vec<RecognizedNodeProvenance>,
    seen_nodes: &mut BTreeSet<String>,
) -> Result<(), LegitimacyError> {
    let file = &files[location.file_index];
    let handler = &file.ast.handlers[location.handler_index];
    let id = handler_id(files, location);
    let default = handler
        .default_result
        .as_ref()
        .map(result_to_graph)
        .unwrap_or(Decision::Escalate);
    add_node_once(
        builder,
        nodes,
        seen_nodes,
        binary_node(&id, handler_decision_gates(handler), default)?,
        recognized_node(
            &id,
            &handler.name,
            &file.path,
            &file.ast,
            Some(&handler.span),
        ),
    )
}

fn add_node_once(
    builder: &mut GraphBuilder,
    nodes: &mut Vec<RecognizedNodeProvenance>,
    seen_nodes: &mut BTreeSet<String>,
    node: GovernanceNode,
    provenance: RecognizedNodeProvenance,
) -> Result<(), LegitimacyError> {
    if seen_nodes.insert(provenance.node_id.clone()) {
        *builder = std::mem::replace(builder, GraphBuilder::new()?).add_node(node)?;
        nodes.push(provenance);
    }
    Ok(())
}

fn resolve_handler(
    files: &[TypeScriptApprovalCoreFile],
    handler_index: &BTreeMap<String, Vec<HandlerLocation>>,
    path: &str,
    registration: &TypeScriptApprovalCoreRegistration,
    caller: &str,
    resolution_issues: &mut Vec<super::ResolutionIssue>,
) -> Option<HandlerLocation> {
    let candidates = handler_index.get(&registration.handler)?;
    if candidates.len() > 1 {
        resolution_issues.push(super::ResolutionIssue {
            caller: caller.to_string(),
            target_symbol: registration.handler.clone(),
            kind: super::ResolutionIssueKind::Ambiguous,
            candidates: candidates
                .iter()
                .map(|location| handler_id(files, *location))
                .collect(),
        });
    }
    candidates
        .iter()
        .copied()
        .find(|location| files[location.file_index].path == path)
        .or_else(|| candidates.first().copied())
}

fn registration_node_id(path: &str, registration: &TypeScriptApprovalCoreRegistration) -> String {
    format!(
        "{path}::registration::{}::{}",
        registration.surface, registration.handler
    )
}

fn handler_id(files: &[TypeScriptApprovalCoreFile], location: HandlerLocation) -> String {
    let file = &files[location.file_index];
    let handler = &file.ast.handlers[location.handler_index];
    format!("{}::{}", file.path, handler.name)
}

fn binary_node(
    id: &str,
    gates: Vec<Gate>,
    default: Decision,
) -> Result<GovernanceNode, LegitimacyError> {
    Ok(GovernanceNode::Binary {
        id: NodeId::new(id)?,
        name: id.to_string(),
        gates,
        default,
        combination: GateLogic::FirstMatch,
    })
}

fn recognized_node(
    id: &str,
    name: &str,
    path: &str,
    ast: &TypeScriptApprovalCoreAst,
    span: Option<&TypeScriptApprovalCoreSourceSpan>,
) -> RecognizedNodeProvenance {
    let span = span.cloned().unwrap_or(TypeScriptApprovalCoreSourceSpan {
        line_start: 1,
        line_end: 1,
    });
    RecognizedNodeProvenance {
        node_id: id.to_string(),
        function_name: name.to_string(),
        relative_path: path.to_string(),
        language: ExtractionSourceLanguage::TypeScript,
        line_start: span.line_start,
        line_end: span.line_end,
        confidence: RecognitionConfidence::High,
        tier: ExtractionEvidenceTier::Automatic,
        rationale: vec![
            "theorem-backed TypeScriptApprovalCore extraction".to_string(),
            format!("canonical AST hash {}", ast.canonical_hash),
            format!("Lean theorem {EXTRACTION_THEOREM}"),
            format!("Lean theorem {FAILURE_THEOREM}"),
        ],
    }
}

fn union_decision_gates(literals: &[String]) -> Vec<Gate> {
    literals
        .iter()
        .filter_map(|literal| {
            approval_result_from_literal(literal).map(|result| Gate::ExactMatch {
                value: literal.clone(),
                decision: result_to_graph(&result),
            })
        })
        .collect()
}

fn handler_decision_gates(handler: &TypeScriptApprovalCoreHandler) -> Vec<Gate> {
    handler
        .results
        .iter()
        .map(|result| Gate::ExactMatch {
            value: approval_result_literal(result).to_string(),
            decision: result_to_graph(result),
        })
        .collect()
}

fn result_to_graph(result: &TypeScriptApprovalCoreApprovalResult) -> Decision {
    match result {
        TypeScriptApprovalCoreApprovalResult::Allow => Decision::Permit,
        TypeScriptApprovalCoreApprovalResult::Ask
        | TypeScriptApprovalCoreApprovalResult::Escalate => Decision::Escalate,
        TypeScriptApprovalCoreApprovalResult::Deny => Decision::Deny,
    }
}
