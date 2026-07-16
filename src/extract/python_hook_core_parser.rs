use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};
use tree_sitter::{Node, Parser};
use unicode_ident::{is_xid_continue, is_xid_start};

const CORE_HASH_ALGORITHM: &str = "python-hook-core-json-sha256:v1";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsupportedConstruct {
    pub message: String,
    pub line: Option<usize>,
}

impl UnsupportedConstruct {
    fn new(message: impl Into<String>, node: Option<Node<'_>>) -> Self {
        Self {
            message: message.into(),
            line: node.map(|node| node.start_position().row + 1),
        }
    }
}

impl fmt::Display for UnsupportedConstruct {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.line {
            Some(line) => write!(
                formatter,
                "unsupported PythonHookCore construct at line {line}: {}",
                self.message
            ),
            None => write!(
                formatter,
                "unsupported PythonHookCore construct: {}",
                self.message
            ),
        }
    }
}

impl std::error::Error for UnsupportedConstruct {}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PythonHookCoreAst {
    pub hash_algorithm: String,
    pub canonical_hash: String,
    pub literal_unions: Vec<PythonHookCoreLiteralUnion>,
    pub schemas: Vec<PythonHookCoreSchema>,
    pub dispatch_enums: Vec<PythonHookCoreDispatchEnum>,
    pub callbacks: Vec<PythonHookCoreCallback>,
    pub registrations: Vec<PythonHookCoreRegistration>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PythonHookCoreLiteralUnion {
    pub name: String,
    pub literals: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PythonHookCoreSchema {
    pub name: String,
    pub kind: PythonHookCoreSchemaKind,
    pub fields: Vec<PythonHookCoreField>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum PythonHookCoreSchemaKind {
    Dataclass,
    TypedDict,
    PydanticModel,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PythonHookCoreField {
    pub name: String,
    pub literals: Vec<String>,
    pub decision_position: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PythonHookCoreDispatchEnum {
    pub name: String,
    pub variants: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PythonHookCoreCallback {
    pub name: String,
    pub decisions: Vec<PythonHookCoreDecision>,
    pub default_decision: Option<PythonHookCoreDecision>,
    pub calls: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PythonHookCoreRegistration {
    pub event: String,
    pub callback: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum PythonHookCoreDecision {
    Allow,
    Deny,
    Ask,
    Block,
}

pub fn parse_python_hook_core(source: &str) -> Result<PythonHookCoreAst, UnsupportedConstruct> {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_python::LANGUAGE.into())
        .map_err(|error| {
            UnsupportedConstruct::new(format!("failed to load Python grammar: {error}"), None)
        })?;
    let tree = parser
        .parse(source, None)
        .ok_or_else(|| UnsupportedConstruct::new("tree-sitter returned no parse tree", None))?;
    if tree.root_node().has_error() {
        return Err(UnsupportedConstruct::new(
            "source contains Python parse errors",
            Some(tree.root_node()),
        ));
    }

    let mut builder = CoreAstBuilder::default();
    builder.collect_module(tree.root_node(), source)?;
    builder.finish(source)
}

#[derive(Default)]
struct CoreAstBuilder {
    literal_unions: Vec<PythonHookCoreLiteralUnion>,
    schemas: Vec<PythonHookCoreSchema>,
    dispatch_enums: Vec<PythonHookCoreDispatchEnum>,
    callbacks: BTreeMap<String, PythonHookCoreCallback>,
    registrations: Vec<PythonHookCoreRegistration>,
    shadowed_names: BTreeSet<String>,
    decision_type_names: BTreeSet<String>,
}

impl CoreAstBuilder {
    fn collect_module(&mut self, root: Node<'_>, source: &str) -> Result<(), UnsupportedConstruct> {
        let mut cursor = root.walk();
        for child in root.named_children(&mut cursor) {
            self.collect_top_level(child, source)?;
        }
        Ok(())
    }

    fn collect_top_level(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        match node.kind() {
            "comment"
            | "import_statement"
            | "import_from_statement"
            | "future_import_statement" => Ok(()),
            "expression_statement" => self.collect_expression_statement(node, source),
            "class_definition" => self.collect_class(node, source, false),
            "function_definition" => self.collect_function(node, source, Vec::new()),
            "decorated_definition" => self.collect_decorated(node, source),
            "if_statement" => self.collect_top_level_if(node, source),
            _ => Err(UnsupportedConstruct::new(
                format!("top-level '{}' is outside PythonHookCore", node.kind()),
                Some(node),
            )),
        }
    }

    fn collect_decorated(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let decorators = decorator_texts(node, source)?;
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "class_definition" => {
                    let is_dataclass = decorators
                        .iter()
                        .any(|text| decorator_has_name(text, "dataclass"));
                    return self.collect_class(child, source, is_dataclass);
                }
                "function_definition" => return self.collect_function(child, source, decorators),
                "decorator" => {}
                _ => {
                    return Err(UnsupportedConstruct::new(
                        format!("decorated '{}' is outside PythonHookCore", child.kind()),
                        Some(child),
                    ));
                }
            }
        }
        Err(UnsupportedConstruct::new(
            "decorated definition has no class or function",
            Some(node),
        ))
    }

    fn collect_expression_statement(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let snippet = text(node, source)?.trim();
        if snippet.is_empty() || is_string_expression(node) {
            return Ok(());
        }
        if let Some(assignment) = first_named_child(node, "assignment") {
            return self.collect_assignment(assignment, source);
        }
        if snippet == "pass" || snippet.starts_with("__all__") {
            return Ok(());
        }
        Err(UnsupportedConstruct::new(
            "only docstrings, assignments, imports, classes, and functions are supported at top level",
            Some(node),
        ))
    }

    fn collect_assignment(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let snippet = text(node, source)?.trim();
        let target = assignment_target(node, source)?.unwrap_or_default();
        if target.is_empty() {
            return Ok(());
        }

        let literals = extract_string_literals_from_text(snippet);
        if snippet.contains("Literal[")
            || snippet.contains("Literal [")
            || snippet.contains("Literal\n")
        {
            let stable = stable_literals(literals);
            if stable
                .iter()
                .any(|literal| decision_from_literal(literal).is_some())
            {
                self.decision_type_names.insert(target.clone());
            }
            self.literal_unions.push(PythonHookCoreLiteralUnion {
                name: target,
                literals: stable,
            });
            return Ok(());
        }
        if self.collect_registration_assignment(node, source)? {
            return Ok(());
        }

        if self.callbacks.contains_key(&target) {
            self.shadowed_names.insert(target.clone());
        }
        if looks_hook_related(&target)
            && literals
                .iter()
                .any(|literal| decision_from_literal(literal).is_some())
        {
            return Err(UnsupportedConstruct::new(
                "decision literals in untyped top-level assignments are not PythonHookCore",
                Some(node),
            ));
        }
        Ok(())
    }

    fn collect_registration_assignment(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<bool, UnsupportedConstruct> {
        let Some(value) = assignment_value(node) else {
            return Ok(false);
        };
        let prior = self.registrations.len();
        self.collect_registration_node(value, source)?;
        Ok(self.registrations.len() != prior)
    }

    fn collect_registration_node(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        if node.kind() == "pair"
            && let (Some(key), Some(value)) = (
                node.child_by_field_name("key"),
                node.child_by_field_name("value"),
            )
        {
            let events = extract_string_literals_from_text(text(key, source)?);
            let identifiers = extract_identifiers(text(value, source)?);
            self.add_registrations(events, identifiers);
        }
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            self.collect_registration_node(child, source)?;
        }
        Ok(())
    }

    fn add_registrations(&mut self, events: Vec<String>, identifiers: BTreeSet<String>) {
        for event in events {
            for callback in identifiers
                .iter()
                .filter(|name| !is_registration_keyword(name))
            {
                self.registrations.push(PythonHookCoreRegistration {
                    event: event.clone(),
                    callback: callback.clone(),
                });
            }
        }
    }

    fn collect_class(
        &mut self,
        node: Node<'_>,
        source: &str,
        decorated_dataclass: bool,
    ) -> Result<(), UnsupportedConstruct> {
        let name = named_field_text(node, "name", source)?.to_string();
        let body = node.child_by_field_name("body").ok_or_else(|| {
            UnsupportedConstruct::new(format!("class '{name}' has no body"), Some(node))
        })?;
        let bases = class_base_names(node, source)?;
        let kind = if decorated_dataclass {
            Some(PythonHookCoreSchemaKind::Dataclass)
        } else if bases.contains("TypedDict") {
            Some(PythonHookCoreSchemaKind::TypedDict)
        } else if bases.contains("BaseModel") {
            Some(PythonHookCoreSchemaKind::PydanticModel)
        } else if is_schema_like_subclass_name(&name) {
            Some(PythonHookCoreSchemaKind::TypedDict)
        } else if bases.contains("Protocol") && !class_body_has_literal_annotation(body, source)? {
            return Ok(());
        } else if bases.contains("Enum") {
            self.collect_dispatch_enum(node, source, name)?;
            return Ok(());
        } else {
            None
        };

        let Some(kind) = kind else {
            return Err(UnsupportedConstruct::new(
                format!("class '{name}' is not a dataclass, TypedDict, Pydantic model, or Enum"),
                Some(node),
            ));
        };

        let mut fields = Vec::new();
        for (field_name, annotation) in class_field_annotations(body, source)? {
            let literals = stable_literals(extract_string_literals_from_text(&annotation));
            let decision_literals = literals
                .iter()
                .any(|literal| decision_from_literal(literal).is_some());
            let decision_position = is_decision_annotation(&annotation, &self.decision_type_names);
            if decision_literals && !decision_position {
                return Err(UnsupportedConstruct::new(
                    format!(
                        "field '{field_name}' uses decision literals but is not a typed decision position"
                    ),
                    Some(body),
                ));
            }
            fields.push(PythonHookCoreField {
                name: field_name,
                literals,
                decision_position,
            });
        }

        self.schemas
            .push(PythonHookCoreSchema { name, kind, fields });
        Ok(())
    }

    fn collect_dispatch_enum(
        &mut self,
        node: Node<'_>,
        source: &str,
        name: String,
    ) -> Result<(), UnsupportedConstruct> {
        let body = node.child_by_field_name("body").ok_or_else(|| {
            UnsupportedConstruct::new(format!("enum '{name}' has no body"), Some(node))
        })?;
        self.dispatch_enums.push(PythonHookCoreDispatchEnum {
            name,
            variants: stable_literals(extract_string_literals_from_text(text(body, source)?)),
        });
        Ok(())
    }

    fn collect_function(
        &mut self,
        node: Node<'_>,
        source: &str,
        decorators: Vec<String>,
    ) -> Result<(), UnsupportedConstruct> {
        let name = named_field_text(node, "name", source)?.to_string();
        let function_text = text(node, source)?;
        let typed_decision = function_return_annotation(function_text).is_some_and(|annotation| {
            is_decision_annotation(annotation, &self.decision_type_names)
        });
        let body = node.child_by_field_name("body").ok_or_else(|| {
            UnsupportedConstruct::new(format!("function '{name}' has no body"), Some(node))
        })?;
        let mut collector = CallbackCollector::new(typed_decision);
        collector.collect_block(body, source)?;
        if collector.saw_decision_literal && !typed_decision {
            return Err(UnsupportedConstruct::new(
                format!(
                    "function '{name}' returns decision literals without a typed decision annotation"
                ),
                Some(node),
            ));
        }

        let decisions = collector.decisions.into_iter().collect::<Vec<_>>();
        if !decisions.is_empty() {
            self.callbacks.insert(
                name.clone(),
                PythonHookCoreCallback {
                    name: name.clone(),
                    default_decision: decisions.last().cloned(),
                    decisions,
                    calls: collector.calls.into_iter().collect(),
                },
            );
        }

        for decorator in decorators {
            if is_registration_decorator(&decorator) {
                for event in extract_string_literals_from_text(&decorator) {
                    self.registrations.push(PythonHookCoreRegistration {
                        event,
                        callback: name.clone(),
                    });
                }
            }
        }
        Ok(())
    }

    fn collect_top_level_if(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "block" | "else_clause" | "elif_clause" => {
                    self.collect_import_guard_block(child, source)?
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn collect_import_guard_block(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "import_statement" | "import_from_statement" | "comment" => {}
                "expression_statement" => {
                    let snippet = text(child, source)?.trim();
                    if is_string_expression(child)
                        || snippet.contains(" = Any")
                        || snippet == "pass"
                    {
                        continue;
                    }
                    return Err(UnsupportedConstruct::new(
                        "top-level conditional blocks may only contain imports, docstrings, pass, or type-checking aliases",
                        Some(child),
                    ));
                }
                "block" | "else_clause" | "elif_clause" => {
                    self.collect_import_guard_block(child, source)?
                }
                _ => {
                    return Err(UnsupportedConstruct::new(
                        "top-level conditionals are supported only for import/type-checking guards",
                        Some(child),
                    ));
                }
            }
        }
        Ok(())
    }

    fn finish(mut self, source: &str) -> Result<PythonHookCoreAst, UnsupportedConstruct> {
        for registration in &self.registrations {
            if self.shadowed_names.contains(&registration.callback) {
                return Err(UnsupportedConstruct::new(
                    format!(
                        "registered callback '{}' is shadowed by a later assignment",
                        registration.callback
                    ),
                    None,
                ));
            }
        }
        self.registrations.sort_by(|left, right| {
            left.event
                .cmp(&right.event)
                .then(left.callback.cmp(&right.callback))
        });
        self.registrations
            .dedup_by(|left, right| left.event == right.event && left.callback == right.callback);
        let callbacks = self.callbacks.into_values().collect::<Vec<_>>();
        let mut ast = PythonHookCoreAst {
            hash_algorithm: CORE_HASH_ALGORITHM.to_string(),
            canonical_hash: String::new(),
            literal_unions: sorted_by_name(self.literal_unions),
            schemas: sorted_by_name(self.schemas),
            dispatch_enums: sorted_by_name(self.dispatch_enums),
            callbacks,
            registrations: self.registrations,
        };
        ast.canonical_hash = core_ast_hash(source, &ast)?;
        Ok(ast)
    }
}

struct CallbackCollector {
    typed_decision: bool,
    saw_decision_literal: bool,
    terminated: bool,
    decisions: BTreeSet<PythonHookCoreDecision>,
    calls: BTreeSet<String>,
}

impl CallbackCollector {
    fn new(typed_decision: bool) -> Self {
        Self {
            typed_decision,
            saw_decision_literal: false,
            terminated: false,
            decisions: BTreeSet::new(),
            calls: BTreeSet::new(),
        }
    }

    fn collect_block(&mut self, node: Node<'_>, source: &str) -> Result<(), UnsupportedConstruct> {
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if self.terminated {
                break;
            }
            self.collect_statement(child, source)?;
        }
        Ok(())
    }

    fn collect_statement(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        match node.kind() {
            "comment" | "pass_statement" => Ok(()),
            "block" => self.collect_block(node, source),
            "expression_statement" if is_string_expression(node) => Ok(()),
            "return_statement" => {
                self.collect_return(node, source)?;
                self.terminated = true;
                Ok(())
            }
            "if_statement" | "elif_clause" | "else_clause" => {
                self.collect_calls(node, source)?;
                let mut cursor = node.walk();
                for child in node.named_children(&mut cursor) {
                    if matches!(child.kind(), "block" | "elif_clause" | "else_clause") {
                        let prior_terminated = self.terminated;
                        self.terminated = false;
                        self.collect_block(child, source)?;
                        self.terminated = prior_terminated;
                    }
                }
                Ok(())
            }
            "expression_statement" | "assignment" => {
                let snippet = text(node, source)?;
                if extract_string_literals_from_text(snippet)
                    .iter()
                    .any(|literal| decision_from_literal(literal).is_some())
                {
                    self.saw_decision_literal = true;
                }
                self.collect_calls(node, source)
            }
            _ if self.typed_decision => Err(UnsupportedConstruct::new(
                format!(
                    "typed decision callback contains unsupported '{}'",
                    node.kind()
                ),
                Some(node),
            )),
            _ => Ok(()),
        }
    }

    fn collect_return(&mut self, node: Node<'_>, source: &str) -> Result<(), UnsupportedConstruct> {
        let snippet = text(node, source)?;
        for literal in extract_string_literals_from_text(snippet) {
            if let Some(decision) = decision_from_literal(&literal) {
                self.saw_decision_literal = true;
                self.decisions.insert(decision);
            }
        }
        self.collect_calls(node, source)
    }

    fn collect_calls(&mut self, node: Node<'_>, source: &str) -> Result<(), UnsupportedConstruct> {
        if node.kind() == "call"
            && let Some(function) = node.child_by_field_name("function")
            && let Some(name) = call_target_name(function, source)?
        {
            self.calls.insert(name);
        }
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            self.collect_calls(child, source)?;
        }
        Ok(())
    }
}

pub(crate) fn decision_literal(decision: &PythonHookCoreDecision) -> &'static str {
    match decision {
        PythonHookCoreDecision::Allow => "allow",
        PythonHookCoreDecision::Deny => "deny",
        PythonHookCoreDecision::Ask => "ask",
        PythonHookCoreDecision::Block => "block",
    }
}

trait NamedCore {
    fn name(&self) -> &str;
}

impl NamedCore for PythonHookCoreLiteralUnion {
    fn name(&self) -> &str {
        &self.name
    }
}
impl NamedCore for PythonHookCoreSchema {
    fn name(&self) -> &str {
        &self.name
    }
}
impl NamedCore for PythonHookCoreDispatchEnum {
    fn name(&self) -> &str {
        &self.name
    }
}

fn sorted_by_name<T: NamedCore>(mut values: Vec<T>) -> Vec<T> {
    values.sort_by(|left, right| left.name().cmp(right.name()));
    values
}

fn core_ast_hash(source: &str, ast: &PythonHookCoreAst) -> Result<String, UnsupportedConstruct> {
    let mut normalized = ast.clone();
    normalized.canonical_hash.clear();
    let json = serde_json::to_vec(&normalized).map_err(|error| {
        UnsupportedConstruct::new(format!("failed to serialize core AST: {error}"), None)
    })?;
    let mut hasher = Sha256::new();
    hasher.update(CORE_HASH_ALGORITHM.as_bytes());
    hasher.update([0]);
    hasher.update(json);
    hasher.update([0]);
    hasher.update(source.as_bytes());
    let digest = hasher.finalize();
    Ok(format!(
        "sha256:{}",
        digest
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    ))
}

fn class_field_annotations(
    body: Node<'_>,
    source: &str,
) -> Result<Vec<(String, String)>, UnsupportedConstruct> {
    let mut fields = Vec::new();
    let mut cursor = body.walk();
    for child in body.named_children(&mut cursor) {
        if child.kind() == "function_definition"
            || child.kind() == "decorated_definition"
            || is_string_expression(child)
        {
            continue;
        }
        let snippet = text(child, source)?.trim();
        let Some((name, annotation)) = snippet.split_once(':') else {
            continue;
        };
        let name = name.trim();
        if name.is_empty() || name.contains(' ') {
            continue;
        }
        let annotation = annotation
            .split_once('=')
            .map(|(left, _)| left)
            .unwrap_or(annotation);
        fields.push((name.to_string(), annotation.trim().to_string()));
    }
    Ok(fields)
}

fn class_body_has_literal_annotation(
    body: Node<'_>,
    source: &str,
) -> Result<bool, UnsupportedConstruct> {
    Ok(class_field_annotations(body, source)?
        .iter()
        .any(|(_, annotation)| annotation_mentions_type(annotation, "Literal")))
}

fn class_base_names(
    node: Node<'_>,
    source: &str,
) -> Result<BTreeSet<String>, UnsupportedConstruct> {
    let Some(superclasses) = node.child_by_field_name("superclasses") else {
        return Ok(BTreeSet::new());
    };
    let raw = text(superclasses, source)?
        .trim()
        .trim_start_matches('(')
        .trim_end_matches(')');
    Ok(split_top_level_commas(raw)
        .into_iter()
        .filter(|base| !base.contains('='))
        .filter_map(type_tail_name)
        .collect())
}

fn function_return_annotation(function_text: &str) -> Option<&str> {
    let header = function_text.lines().next()?;
    header
        .split_once("->")
        .map(|(_, annotation)| annotation.trim())
}

fn is_decision_annotation(annotation: &str, decision_type_names: &BTreeSet<String>) -> bool {
    (annotation_mentions_type(annotation, "Literal")
        && extract_string_literals_from_text(annotation)
            .iter()
            .any(|literal| decision_from_literal(literal).is_some()))
        || identifier_tokens(annotation).iter().any(|name| {
            decision_type_names.contains(name)
                || matches!(name.as_str(), "Allow" | "Deny" | "Ask" | "Block")
        })
}

fn is_schema_like_subclass_name(name: &str) -> bool {
    [
        "Input",
        "Output",
        "Config",
        "Context",
        "Status",
        "Options",
        "Result",
        "Definition",
        "Category",
        "Info",
        "Annotations",
        "Response",
    ]
    .iter()
    .any(|suffix| name.ends_with(suffix))
}

pub(crate) fn decision_from_literal(literal: &str) -> Option<PythonHookCoreDecision> {
    match literal {
        "allow" | "approve" => Some(PythonHookCoreDecision::Allow),
        "deny" => Some(PythonHookCoreDecision::Deny),
        "ask" | "defer" => Some(PythonHookCoreDecision::Ask),
        "block" => Some(PythonHookCoreDecision::Block),
        _ => None,
    }
}

fn is_registration_keyword(name: &str) -> bool {
    matches!(
        name,
        "hooks" | "hook" | "matcher" | "timeout" | "none" | "true" | "false" | "dict" | "list"
    )
}

fn looks_hook_related(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.contains("hook") || lower.contains("permission") || lower.contains("decision")
}

fn stable_literals(literals: Vec<String>) -> Vec<String> {
    let mut literals = literals;
    literals.sort();
    literals.dedup();
    literals
}

fn split_top_level_commas(text: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (index, character) in text.char_indices() {
        match character {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                parts.push(text[start..index].trim());
                start = index + 1;
            }
            _ => {}
        }
    }
    if start < text.len() {
        parts.push(text[start..].trim());
    }
    parts
}

fn decorator_has_name(decorator: &str, name: &str) -> bool {
    let body = decorator.trim().trim_start_matches('@').trim();
    let callee = body.split_once('(').map_or(body, |(left, _)| left);
    type_tail_name(callee).is_some_and(|tail| tail == name)
}

fn is_registration_decorator(decorator: &str) -> bool {
    let body = decorator.trim().trim_start_matches('@').trim();
    let callee = body.split_once('(').map_or(body, |(left, _)| left);
    type_tail_name(callee)
        .is_some_and(|tail| matches!(tail.as_str(), "hook" | "register" | "register_hook"))
}

fn annotation_mentions_type(annotation: &str, name: &str) -> bool {
    identifier_tokens(annotation)
        .iter()
        .any(|token| token == name)
}

fn type_tail_name(text: &str) -> Option<String> {
    let head = text.split(['[', '(']).next().unwrap_or(text).trim();
    identifier_tokens(head).last().cloned()
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

fn identifier_tokens(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    for character in text.chars() {
        if current.is_empty() {
            if is_python_identifier_start(character) {
                current.push(character);
            }
        } else if is_python_identifier_continue(character) {
            current.push(character);
        } else {
            tokens.push(std::mem::take(&mut current));
        }
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

fn is_python_identifier_start(character: char) -> bool {
    character == '_' || is_xid_start(character)
}

fn is_python_identifier_continue(character: char) -> bool {
    character == '_' || is_xid_continue(character)
}

fn extract_identifiers(text: &str) -> BTreeSet<String> {
    identifier_tokens(text).into_iter().collect()
}

fn assignment_target(node: Node<'_>, source: &str) -> Result<Option<String>, UnsupportedConstruct> {
    node.child_by_field_name("left")
        .or_else(|| node.child_by_field_name("target"))
        .map(|target| text(target, source).map(|value| value.trim().to_string()))
        .transpose()
}

fn assignment_value<'tree>(node: Node<'tree>) -> Option<Node<'tree>> {
    node.child_by_field_name("right")
        .or_else(|| node.child_by_field_name("value"))
}

fn decorator_texts(node: Node<'_>, source: &str) -> Result<Vec<String>, UnsupportedConstruct> {
    let mut texts = Vec::new();
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        if child.kind() == "decorator" {
            texts.push(text(child, source)?.to_string());
        }
    }
    Ok(texts)
}

fn first_named_child<'tree>(node: Node<'tree>, kind: &str) -> Option<Node<'tree>> {
    let mut cursor = node.walk();
    node.named_children(&mut cursor)
        .find(|child| child.kind() == kind)
}

fn named_field_text<'a>(
    node: Node<'_>,
    field: &str,
    source: &'a str,
) -> Result<&'a str, UnsupportedConstruct> {
    node.child_by_field_name(field)
        .ok_or_else(|| {
            UnsupportedConstruct::new(format!("missing required field '{field}'"), Some(node))
        })
        .and_then(|field| text(field, source))
}

fn call_target_name(node: Node<'_>, source: &str) -> Result<Option<String>, UnsupportedConstruct> {
    match node.kind() {
        "identifier" => Ok(Some(text(node, source)?.to_ascii_lowercase())),
        "attribute" => node
            .child_by_field_name("attribute")
            .map(|attribute| text(attribute, source).map(|name| name.to_ascii_lowercase()))
            .transpose(),
        _ => Ok(None),
    }
}

fn is_string_expression(node: Node<'_>) -> bool {
    if node.kind() == "string" {
        return true;
    }
    let mut cursor = node.walk();
    let children = node.named_children(&mut cursor).collect::<Vec<_>>();
    children.len() == 1 && children[0].kind() == "string"
}

fn text<'a>(node: Node<'_>, source: &'a str) -> Result<&'a str, UnsupportedConstruct> {
    node.utf8_text(source.as_bytes()).map_err(|error| {
        UnsupportedConstruct::new(
            format!("failed to read syntax node text: {error}"),
            Some(node),
        )
    })
}
