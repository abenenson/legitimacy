use super::{
    ExtractionCoverageReport, ExtractionEvidenceTier, ExtractionFileReport, ExtractionFileStatus,
    ExtractionOptions, ExtractionSourceLanguage, GovernanceExtractionArtifacts,
    RecognitionConfidence, RecognizedEdgeProvenance, RecognizedNodeProvenance, SourceLanguage,
    collect_source_files,
    python_hook_core_parser::{
        PythonHookCoreAst, PythonHookCoreCallback, PythonHookCoreDecision, decision_from_literal,
        decision_literal, parse_python_hook_core,
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
use tree_sitter::{Node, Parser};

const EXTRACTION_THEOREM: &str = "extractPythonHookCore_decision_equivalent";
const FAILURE_THEOREM: &str = "python_hook_extractor_failure_reflects_source_failure";

pub(crate) fn extract_python_hook_core_artifacts(
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
        .any(|(_, language)| *language != SourceLanguage::Python)
    {
        return Err(LegitimacyError::invalid_input(
            "theorem-backed PythonHookCore mode accepts Python source files only",
        ));
    }
    if options.allow_partial {
        return Err(LegitimacyError::invalid_input(
            "theorem-backed PythonHookCore mode refuses unsupported constructs instead of partial extraction",
        ));
    }

    let mut files = Vec::new();
    let mut reports = Vec::new();
    for (path, _) in source_files {
        let source = fs::read_to_string(&path).map_err(|source| LegitimacyError::Io {
            context: format!("PythonHookCore source '{}'", path.display()),
            source,
        })?;
        let relative_path = path
            .strip_prefix(source_dir)
            .unwrap_or(path.as_path())
            .to_string_lossy()
            .replace('\\', "/");
        match parse_python_hook_core(&source) {
            Ok(ast) => {
                reports.push(ExtractionFileReport {
                    path: relative_path.clone(),
                    language: ExtractionSourceLanguage::Python,
                    status: ExtractionFileStatus::Parsed,
                    detail: Some(format!("PythonHookCore AST {}", ast.canonical_hash)),
                });
                let spans = source_span_index(&source)?;
                files.push(PythonHookCoreFile {
                    path: relative_path,
                    ast,
                    spans,
                });
            }
            Err(error) => {
                reports.push(ExtractionFileReport {
                    path: relative_path,
                    language: ExtractionSourceLanguage::Python,
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
        resolution_issues: Vec::new(),
        review_overlay: None,
        boundary_causal_safety: BoundaryCausalSafetyAssessment::default(),
    })
}

struct CoreGraphBuild {
    graph: GovernanceGraph,
    nodes: Vec<RecognizedNodeProvenance>,
    edges: Vec<RecognizedEdgeProvenance>,
}

struct PythonHookCoreFile {
    path: String,
    ast: PythonHookCoreAst,
    spans: PythonSourceSpanIndex,
}

#[derive(Clone, Copy, Debug, Default)]
struct SourceSpan {
    line_start: usize,
    line_end: usize,
}

impl SourceSpan {
    fn from_node(node: Node<'_>) -> Self {
        Self {
            line_start: node.start_position().row + 1,
            line_end: node.end_position().row + 1,
        }
    }
}

#[derive(Default)]
struct PythonSourceSpanIndex {
    literal_unions: BTreeMap<String, SourceSpan>,
    schemas: BTreeMap<String, SourceSpan>,
    callbacks: BTreeMap<String, SourceSpan>,
    registrations: BTreeMap<(String, String), SourceSpan>,
}

fn build_graph(files: Vec<PythonHookCoreFile>) -> Result<CoreGraphBuild, LegitimacyError> {
    let mut builder = GraphBuilder::new()?;
    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut seen_nodes = BTreeSet::new();
    let mut callback_ids = BTreeMap::new();

    for file in &files {
        let path = &file.path;
        let ast = &file.ast;
        for callback in &ast.callbacks {
            callback_ids.insert(
                (path.clone(), callback.name.clone()),
                format!("{path}::{}", callback.name),
            );
        }
    }

    for file in &files {
        let path = &file.path;
        let ast = &file.ast;
        for union in &ast.literal_unions {
            let gates = decision_gates(&union.literals);
            if !gates.is_empty() {
                let id = format!("{path}::{}", union.name);
                if seen_nodes.insert(id.clone()) {
                    builder = builder.add_node(binary_node(&id, gates, Decision::Escalate)?)?;
                    nodes.push(recognized_node(
                        &id,
                        &union.name,
                        path,
                        ast,
                        file.spans.literal_unions.get(&union.name).copied(),
                    ));
                }
            }
        }
        for schema in &ast.schemas {
            let gates = schema
                .fields
                .iter()
                .filter(|field| field.decision_position)
                .flat_map(|field| decision_gates(&field.literals))
                .collect::<Vec<_>>();
            if !gates.is_empty() {
                let id = format!("{path}::{}", schema.name);
                if seen_nodes.insert(id.clone()) {
                    builder = builder.add_node(binary_node(&id, gates, Decision::Escalate)?)?;
                    nodes.push(recognized_node(
                        &id,
                        &schema.name,
                        path,
                        ast,
                        file.spans.schemas.get(&schema.name).copied(),
                    ));
                }
            }
        }
        for registration in &ast.registrations {
            let Some(callback_id) =
                callback_ids.get(&(path.clone(), registration.callback.clone()))
            else {
                continue;
            };
            let registration_id = format!(
                "{path}::registration::{}::{}",
                registration.event, registration.callback
            );
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
                    path,
                    ast,
                    file.spans
                        .registrations
                        .get(&(registration.event.clone(), registration.callback.clone()))
                        .copied(),
                ));
            }

            let callback = ast
                .callbacks
                .iter()
                .find(|candidate| candidate.name == registration.callback)
                .expect("registration was filtered to known callbacks");
            if seen_nodes.insert(callback_id.clone()) {
                builder = builder.add_node(binary_node(
                    callback_id,
                    callback_decision_gates(callback),
                    callback
                        .default_decision
                        .as_ref()
                        .map(decision_to_graph)
                        .unwrap_or(Decision::Escalate),
                )?)?;
                nodes.push(recognized_node(
                    callback_id,
                    &callback.name,
                    path,
                    ast,
                    file.spans.callbacks.get(&callback.name).copied(),
                ));
            }
            builder = builder.add_edge(
                NodeId::new(registration_id.clone())?,
                NodeId::new(callback_id.clone())?,
                EdgeTransform::PassThrough,
            )?;
            edges.push(RecognizedEdgeProvenance {
                from: registration_id,
                to: callback_id.clone(),
                target_symbol: registration.callback.clone(),
                resolution: super::EdgeResolutionKind::SameFile,
                tier: ExtractionEvidenceTier::Automatic,
                review_note: None,
            });
        }
    }

    for file in &files {
        let path = &file.path;
        let ast = &file.ast;
        for registration in &ast.registrations {
            let Some(from) = callback_ids.get(&(path.clone(), registration.callback.clone()))
            else {
                continue;
            };
            let Some(callback) = ast
                .callbacks
                .iter()
                .find(|candidate| candidate.name == registration.callback)
            else {
                continue;
            };
            for call in &callback.calls {
                if let Some(to) = callback_ids.get(&(path.clone(), call.clone()))
                    && from != to
                {
                    builder = builder.add_edge(
                        NodeId::new(from.clone())?,
                        NodeId::new(to.clone())?,
                        EdgeTransform::PassThrough,
                    )?;
                    edges.push(RecognizedEdgeProvenance {
                        from: from.clone(),
                        to: to.clone(),
                        target_symbol: call.clone(),
                        resolution: super::EdgeResolutionKind::SameFile,
                        tier: ExtractionEvidenceTier::Automatic,
                        review_note: None,
                    });
                }
            }
        }
    }

    if nodes.is_empty() {
        return Err(LegitimacyError::invalid_input(
            "no PythonHookCore schema, decision union, or formal hook registration was discovered",
        ));
    }

    Ok(CoreGraphBuild {
        graph: builder.build()?,
        nodes,
        edges,
    })
}

fn source_span_index(source: &str) -> Result<PythonSourceSpanIndex, LegitimacyError> {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_python::LANGUAGE.into())
        .map_err(|error| {
            LegitimacyError::invalid_input(format!(
                "failed to load tree-sitter-python grammar for PythonHookCore spans: {error}"
            ))
        })?;
    let tree = parser.parse(source, None).ok_or_else(|| {
        LegitimacyError::invalid_input("tree-sitter returned no PythonHookCore span parse tree")
    })?;
    if tree.root_node().has_error() {
        return Err(LegitimacyError::invalid_input(
            "failed to recover PythonHookCore source spans from Python parse errors",
        ));
    }

    let mut index = PythonSourceSpanIndex::default();
    let mut cursor = tree.root_node().walk();
    for child in tree.root_node().named_children(&mut cursor) {
        collect_top_level_spans(child, source, &mut index)?;
    }
    Ok(index)
}

fn collect_top_level_spans(
    node: Node<'_>,
    source: &str,
    index: &mut PythonSourceSpanIndex,
) -> Result<(), LegitimacyError> {
    match node.kind() {
        "expression_statement" => {
            let mut cursor = node.walk();
            for child in node.named_children(&mut cursor) {
                if child.kind() == "assignment" {
                    collect_assignment_span(child, source, index)?;
                }
            }
        }
        "assignment" => collect_assignment_span(node, source, index)?,
        "class_definition" => {
            if let Some(name) = named_field_text(node, "name", source)? {
                index
                    .schemas
                    .insert(name.to_string(), SourceSpan::from_node(node));
            }
        }
        "function_definition" => {
            if let Some(name) = named_field_text(node, "name", source)? {
                index
                    .callbacks
                    .insert(name.to_string(), SourceSpan::from_node(node));
            }
        }
        "decorated_definition" => {
            let mut cursor = node.walk();
            for child in node.named_children(&mut cursor) {
                if matches!(child.kind(), "class_definition" | "function_definition") {
                    collect_top_level_spans(child, source, index)?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}

fn collect_assignment_span(
    node: Node<'_>,
    source: &str,
    index: &mut PythonSourceSpanIndex,
) -> Result<(), LegitimacyError> {
    let Some(target) = assignment_target_name(node, source)? else {
        return Ok(());
    };
    let snippet = text(node, source)?.to_string();
    let span = SourceSpan::from_node(node);
    if snippet.contains("Literal[")
        || snippet.contains("Literal [")
        || snippet.contains("Literal\n")
    {
        index.literal_unions.insert(target.clone(), span);
    }
    if let Some(value) = assignment_value(node) {
        collect_registration_spans(value, source, span, index)?;
    }
    Ok(())
}

fn collect_registration_spans(
    node: Node<'_>,
    source: &str,
    span: SourceSpan,
    index: &mut PythonSourceSpanIndex,
) -> Result<(), LegitimacyError> {
    if node.kind() == "pair"
        && let (Some(key), Some(value)) = (
            node.child_by_field_name("key"),
            node.child_by_field_name("value"),
        )
    {
        let events = extract_string_literals_from_text(text(key, source)?);
        let callbacks = identifier_nodes(value, source)?;
        for event in events {
            for callback in &callbacks {
                index
                    .registrations
                    .insert((event.clone(), callback.clone()), span);
            }
        }
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_registration_spans(child, source, span, index)?;
    }
    Ok(())
}

fn identifier_nodes(node: Node<'_>, source: &str) -> Result<BTreeSet<String>, LegitimacyError> {
    let mut identifiers = BTreeSet::new();
    collect_identifier_nodes(node, source, &mut identifiers)?;
    Ok(identifiers)
}

fn collect_identifier_nodes(
    node: Node<'_>,
    source: &str,
    identifiers: &mut BTreeSet<String>,
) -> Result<(), LegitimacyError> {
    if node.kind() == "identifier" {
        identifiers.insert(text(node, source)?.to_string());
        return Ok(());
    }
    if matches!(node.kind(), "comment" | "string") {
        return Ok(());
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_identifier_nodes(child, source, identifiers)?;
    }
    Ok(())
}

fn assignment_target_name(node: Node<'_>, source: &str) -> Result<Option<String>, LegitimacyError> {
    let candidate = node
        .child_by_field_name("left")
        .or_else(|| node.named_child(0));
    let Some(candidate) = candidate else {
        return Ok(None);
    };
    if candidate.kind() == "identifier" {
        return Ok(Some(text(candidate, source)?.to_string()));
    }
    Ok(None)
}

fn assignment_value<'tree>(node: Node<'tree>) -> Option<Node<'tree>> {
    node.child_by_field_name("right")
        .or_else(|| node.child_by_field_name("value"))
}

fn named_field_text<'a>(
    node: Node<'_>,
    field: &str,
    source: &'a str,
) -> Result<Option<&'a str>, LegitimacyError> {
    node.child_by_field_name(field)
        .map(|child| text(child, source))
        .transpose()
}

fn text<'a>(node: Node<'_>, source: &'a str) -> Result<&'a str, LegitimacyError> {
    node.utf8_text(source.as_bytes()).map_err(|error| {
        LegitimacyError::invalid_input(format!(
            "failed to read PythonHookCore source span text: {error}"
        ))
    })
}

fn extract_string_literals_from_text(text: &str) -> Vec<String> {
    let mut literals = Vec::new();
    let mut quote = None;
    let mut start = 0usize;
    let mut escaped = false;
    for (index, character) in text.char_indices() {
        match (quote, character, escaped) {
            (None, '"' | '\'', _) => {
                quote = Some(character);
                start = index + character.len_utf8();
            }
            (Some(_), '\\', false) => escaped = true,
            (Some(open), current, false) if current == open => {
                literals.push(text[start..index].replace("\\\"", "\"").replace("\\'", "'"));
                quote = None;
            }
            (Some(_), _, true) => escaped = false,
            _ => {}
        }
    }
    literals
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
    ast: &PythonHookCoreAst,
    span: Option<SourceSpan>,
) -> RecognizedNodeProvenance {
    let span = span.unwrap_or(SourceSpan {
        line_start: 1,
        line_end: 1,
    });
    RecognizedNodeProvenance {
        node_id: id.to_string(),
        function_name: name.to_string(),
        relative_path: path.to_string(),
        language: ExtractionSourceLanguage::Python,
        line_start: span.line_start,
        line_end: span.line_end,
        confidence: RecognitionConfidence::High,
        tier: ExtractionEvidenceTier::Automatic,
        rationale: vec![
            "theorem-backed PythonHookCore extraction".to_string(),
            format!("canonical AST hash {}", ast.canonical_hash),
            format!("Lean theorem {EXTRACTION_THEOREM}"),
            format!("Lean theorem {FAILURE_THEOREM}"),
        ],
    }
}

fn callback_decision_gates(callback: &PythonHookCoreCallback) -> Vec<Gate> {
    callback
        .decisions
        .iter()
        .map(|decision| Gate::ExactMatch {
            value: decision_literal(decision).to_string(),
            decision: decision_to_graph(decision),
        })
        .collect()
}

fn decision_gates(literals: &[String]) -> Vec<Gate> {
    literals
        .iter()
        .filter_map(|literal| {
            decision_from_literal(literal).map(|decision| Gate::ExactMatch {
                value: literal.clone(),
                decision: decision_to_graph(&decision),
            })
        })
        .collect()
}

fn decision_to_graph(decision: &PythonHookCoreDecision) -> Decision {
    match decision {
        PythonHookCoreDecision::Allow => Decision::Permit,
        PythonHookCoreDecision::Deny | PythonHookCoreDecision::Block => Decision::Deny,
        PythonHookCoreDecision::Ask => Decision::Escalate,
    }
}
