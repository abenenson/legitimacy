use super::{
    ExtractionCoverageReport, ExtractionEvidenceTier, ExtractionFileReport, ExtractionFileStatus,
    ExtractionOptions, ExtractionSourceLanguage, GovernanceExtractionArtifacts,
    RecognitionConfidence, RecognizedEdgeProvenance, RecognizedNodeProvenance, SourceLanguage,
    collect_source_files,
    rust_hook_core_parser::{
        RustHookCoreAst, RustHookCoreDecision, RustHookCoreHook, RustHookCoreRegistration,
        RustHookCoreSourceSpan, parse_rust_hook_core,
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

const EXTRACTION_THEOREM: &str = "extractRustHookCore_decision_equivalent";
const FAILURE_THEOREM: &str =
    "rust_hook_modeled_program_extractor_failure_reflects_modeled_source_failure";

pub fn build_governance_graph(ast: &RustHookCoreAst) -> GovernanceGraph {
    build_single_ast_graph(ast).expect("RustHookCore AST should build a governance graph")
}

pub(crate) fn extract_rust_hook_core_artifacts(
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
        .any(|(_, language)| *language != SourceLanguage::Rust)
    {
        return Err(LegitimacyError::invalid_input(
            "theorem-backed RustHookCore mode accepts Rust source files only",
        ));
    }
    if options.allow_partial {
        return Err(LegitimacyError::invalid_input(
            "theorem-backed RustHookCore mode refuses unsupported constructs instead of partial extraction",
        ));
    }

    let mut files = Vec::new();
    let mut reports = Vec::new();
    for (path, _) in source_files {
        let source = fs::read_to_string(&path).map_err(|source| LegitimacyError::Io {
            context: format!("RustHookCore source '{}'", path.display()),
            source,
        })?;
        let relative_path = path
            .strip_prefix(source_dir)
            .unwrap_or(path.as_path())
            .to_string_lossy()
            .replace('\\', "/");
        match parse_rust_hook_core(&source) {
            Ok(ast) => {
                reports.push(ExtractionFileReport {
                    path: relative_path.clone(),
                    language: ExtractionSourceLanguage::Rust,
                    status: ExtractionFileStatus::Parsed,
                    detail: Some(format!("RustHookCore AST {}", ast.canonical_hash)),
                });
                files.push(RustHookCoreFile {
                    path: relative_path,
                    ast,
                });
            }
            Err(error) => {
                reports.push(ExtractionFileReport {
                    path: relative_path,
                    language: ExtractionSourceLanguage::Rust,
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

struct RustHookCoreFile {
    path: String,
    ast: RustHookCoreAst,
}

struct CoreGraphBuild {
    graph: GovernanceGraph,
    nodes: Vec<RecognizedNodeProvenance>,
    edges: Vec<RecognizedEdgeProvenance>,
    resolution_issues: Vec<super::ResolutionIssue>,
}

#[derive(Clone, Copy)]
struct HookLocation {
    file_index: usize,
    hook_index: usize,
}

fn build_single_ast_graph(ast: &RustHookCoreAst) -> Result<GovernanceGraph, LegitimacyError> {
    let file = RustHookCoreFile {
        path: "rust_hook_core.rs".to_string(),
        ast: ast.clone(),
    };
    Ok(build_graph(vec![file])?.graph)
}

fn build_graph(files: Vec<RustHookCoreFile>) -> Result<CoreGraphBuild, LegitimacyError> {
    let mut builder = GraphBuilder::new()?;
    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut resolution_issues = Vec::new();
    let mut seen_nodes = BTreeSet::new();
    let mut hook_index: BTreeMap<String, Vec<HookLocation>> = BTreeMap::new();

    for (file_index, file) in files.iter().enumerate() {
        for (hook_index_in_file, hook) in file.ast.hooks.iter().enumerate() {
            hook_index
                .entry(hook.name.clone())
                .or_default()
                .push(HookLocation {
                    file_index,
                    hook_index: hook_index_in_file,
                });
        }
    }

    for file in &files {
        for registration in &file.ast.registrations {
            let registration_id = registration_node_id(&file.path, registration);
            let Some(location) = resolve_hook(
                &files,
                &hook_index,
                &registration.callback,
                &registration_id,
                &mut resolution_issues,
            ) else {
                continue;
            };
            let hook_file = &files[location.file_index];
            let hook = &hook_file.ast.hooks[location.hook_index];
            let hook_id = hook_node_id(&hook_file.path, hook);

            if seen_nodes.insert(registration_id.clone()) {
                builder = builder.add_node(binary_node(
                    &registration_id,
                    vec![Gate::ThresholdGate {
                        field: "hook_registration".to_string(),
                        min: 1.0,
                        decision: Decision::Escalate,
                    }],
                    Decision::Permit,
                )?)?;
                nodes.push(recognized_node(
                    &registration_id,
                    "hook registration",
                    &file.path,
                    &file.ast,
                    registration.source_span,
                ));
            }
            if seen_nodes.insert(hook_id.clone()) {
                builder = builder.add_node(binary_node(
                    &hook_id,
                    hook_decision_gates(hook),
                    hook.default_decision
                        .as_ref()
                        .map(decision_to_graph)
                        .unwrap_or(Decision::Permit),
                )?)?;
                nodes.push(recognized_node(
                    &hook_id,
                    &hook.name,
                    &hook_file.path,
                    &hook_file.ast,
                    hook.source_span,
                ));
            }
            builder = builder.add_edge(
                NodeId::new(registration_id.clone())?,
                NodeId::new(hook_id.clone())?,
                EdgeTransform::PassThrough,
            )?;
            edges.push(RecognizedEdgeProvenance {
                from: registration_id,
                to: hook_id,
                target_symbol: registration.callback.clone(),
                resolution: super::EdgeResolutionKind::GlobalUnique,
                tier: ExtractionEvidenceTier::Automatic,
                review_note: None,
            });
        }
    }

    if nodes.is_empty() {
        return Err(LegitimacyError::invalid_input(
            "no RustHookCore formal hook registration was discovered",
        ));
    }

    Ok(CoreGraphBuild {
        graph: builder.build()?,
        nodes,
        edges,
        resolution_issues,
    })
}

fn resolve_hook(
    files: &[RustHookCoreFile],
    hook_index: &BTreeMap<String, Vec<HookLocation>>,
    callback: &str,
    caller: &str,
    resolution_issues: &mut Vec<super::ResolutionIssue>,
) -> Option<HookLocation> {
    let Some(candidates) = hook_index.get(callback) else {
        resolution_issues.push(super::ResolutionIssue {
            caller: caller.to_string(),
            target_symbol: callback.to_string(),
            kind: super::ResolutionIssueKind::Unresolved,
            candidates: Vec::new(),
        });
        return None;
    };
    if candidates.len() > 1 {
        resolution_issues.push(super::ResolutionIssue {
            caller: caller.to_string(),
            target_symbol: callback.to_string(),
            kind: super::ResolutionIssueKind::Ambiguous,
            candidates: candidates
                .iter()
                .map(|location| {
                    hook_node_id(
                        &files[location.file_index].path,
                        &files[location.file_index].ast.hooks[location.hook_index],
                    )
                })
                .collect(),
        });
    }
    candidates.first().copied()
}

fn registration_node_id(path: &str, registration: &RustHookCoreRegistration) -> String {
    format!(
        "{path}::registration::{}::{}",
        registration.event, registration.callback
    )
}

fn hook_node_id(path: &str, hook: &RustHookCoreHook) -> String {
    format!("{path}::{}", hook.name)
}

fn hook_decision_gates(hook: &RustHookCoreHook) -> Vec<Gate> {
    hook.decisions
        .iter()
        .map(|decision| Gate::ExactMatch {
            value: decision_literal(decision).to_string(),
            decision: decision_to_graph(decision),
        })
        .collect()
}

fn decision_literal(decision: &RustHookCoreDecision) -> &'static str {
    match decision {
        RustHookCoreDecision::Allow => "allow",
        RustHookCoreDecision::Deny => "deny",
        RustHookCoreDecision::Ask => "ask",
        RustHookCoreDecision::Block => "block",
    }
}

fn decision_to_graph(decision: &RustHookCoreDecision) -> Decision {
    match decision {
        RustHookCoreDecision::Allow | RustHookCoreDecision::Ask => Decision::Permit,
        RustHookCoreDecision::Deny | RustHookCoreDecision::Block => Decision::Deny,
    }
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
    ast: &RustHookCoreAst,
    span: RustHookCoreSourceSpan,
) -> RecognizedNodeProvenance {
    RecognizedNodeProvenance {
        node_id: id.to_string(),
        function_name: name.to_string(),
        relative_path: path.to_string(),
        language: ExtractionSourceLanguage::Rust,
        line_start: span.line_start,
        line_end: span.line_end,
        confidence: RecognitionConfidence::High,
        tier: ExtractionEvidenceTier::Automatic,
        rationale: vec![
            "theorem-backed RustHookCore extraction".to_string(),
            format!("canonical AST hash {}", ast.canonical_hash),
            format!("Lean theorem {EXTRACTION_THEOREM}"),
            format!("Lean theorem {FAILURE_THEOREM}"),
        ],
    }
}
