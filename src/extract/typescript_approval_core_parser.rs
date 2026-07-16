use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};
use tree_sitter::{Node, Parser};
use unicode_ident::{is_xid_continue, is_xid_start};

const CORE_HASH_ALGORITHM: &str = "typescript-approval-core-json-sha256:v1";

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
                "unsupported TypeScriptApprovalCore construct at line {line}: {}",
                self.message
            ),
            None => write!(
                formatter,
                "unsupported TypeScriptApprovalCore construct: {}",
                self.message
            ),
        }
    }
}

impl std::error::Error for UnsupportedConstruct {}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeScriptApprovalCoreAst {
    pub hash_algorithm: String,
    pub canonical_hash: String,
    pub approval_unions: Vec<TypeScriptApprovalCoreApprovalUnion>,
    pub requests: Vec<TypeScriptApprovalCoreRequest>,
    pub policies: Vec<TypeScriptApprovalCorePolicy>,
    pub handlers: Vec<TypeScriptApprovalCoreHandler>,
    pub registrations: Vec<TypeScriptApprovalCoreRegistration>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeScriptApprovalCoreApprovalUnion {
    pub name: String,
    pub literals: Vec<String>,
    pub span: TypeScriptApprovalCoreSourceSpan,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeScriptApprovalCoreRequest {
    pub name: String,
    pub fields: Vec<TypeScriptApprovalCoreField>,
    pub span: TypeScriptApprovalCoreSourceSpan,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeScriptApprovalCoreField {
    pub name: String,
    pub type_name: String,
    pub approval_position: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeScriptApprovalCorePolicy {
    pub name: String,
    pub kind: TypeScriptApprovalCorePolicyKind,
    pub entries: Vec<String>,
    pub span: TypeScriptApprovalCoreSourceSpan,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeScriptApprovalCorePolicyKind {
    Allowlist,
    Blocklist,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeScriptApprovalCoreHandler {
    pub name: String,
    pub is_async: bool,
    pub results: Vec<TypeScriptApprovalCoreApprovalResult>,
    pub default_result: Option<TypeScriptApprovalCoreApprovalResult>,
    pub calls: Vec<String>,
    pub fallback_chain: Vec<String>,
    pub span: TypeScriptApprovalCoreSourceSpan,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeScriptApprovalCoreRegistration {
    pub surface: String,
    pub handler: String,
    pub via_decorator: bool,
    pub span: TypeScriptApprovalCoreSourceSpan,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeScriptApprovalCoreSourceSpan {
    pub line_start: usize,
    pub line_end: usize,
}

impl TypeScriptApprovalCoreSourceSpan {
    fn from_node(node: Node<'_>) -> Self {
        Self {
            line_start: node.start_position().row + 1,
            line_end: node.end_position().row + 1,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeScriptApprovalCoreApprovalResult {
    Allow,
    Deny,
    Ask,
    Escalate,
}

pub fn parse_typescript_approval_core(
    source: &str,
) -> Result<TypeScriptApprovalCoreAst, UnsupportedConstruct> {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_typescript::LANGUAGE_TYPESCRIPT.into())
        .map_err(|error| {
            UnsupportedConstruct::new(format!("failed to load TypeScript grammar: {error}"), None)
        })?;
    let tree = parser
        .parse(source, None)
        .ok_or_else(|| UnsupportedConstruct::new("tree-sitter returned no parse tree", None))?;
    if tree.root_node().has_error() {
        return Err(UnsupportedConstruct::new(
            "source contains TypeScript parse errors",
            Some(tree.root_node()),
        ));
    }

    let mut builder = CoreAstBuilder::default();
    builder.collect_declarations(tree.root_node(), source)?;
    builder.collect_handlers(tree.root_node(), source)?;
    builder.finish(source)
}

#[derive(Default)]
struct CoreAstBuilder {
    approval_unions: Vec<TypeScriptApprovalCoreApprovalUnion>,
    requests: Vec<TypeScriptApprovalCoreRequest>,
    policies: Vec<TypeScriptApprovalCorePolicy>,
    handlers: BTreeMap<String, TypeScriptApprovalCoreHandler>,
    registrations: Vec<TypeScriptApprovalCoreRegistration>,
    decision_type_names: BTreeSet<String>,
}

impl CoreAstBuilder {
    fn collect_declarations(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let snippet = text(node, source)?;
        match node.kind() {
            "type_alias_declaration" => self.collect_type_alias(node, snippet)?,
            "interface_declaration" => self.collect_interface(node, snippet)?,
            "lexical_declaration" | "variable_declaration" => {
                self.collect_policy_declaration(node, snippet)?;
            }
            _ => {}
        }
        if matches!(
            node.kind(),
            "program" | "export_statement" | "statement_block" | "ambient_declaration"
        ) {
            let mut cursor = node.walk();
            for child in node.named_children(&mut cursor) {
                self.collect_declarations(child, source)?;
            }
        }
        if node.kind() == "program" {
            self.collect_explicit_registrations(node, source)?;
        }
        Ok(())
    }

    fn collect_handlers(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        match node.kind() {
            "function_declaration" | "method_definition" => self.collect_function(node, source)?,
            "lexical_declaration" | "variable_declaration" => {
                self.collect_arrow_function(node, source)?
            }
            _ => {}
        }
        if matches!(
            node.kind(),
            "program" | "export_statement" | "statement_block" | "ambient_declaration"
        ) {
            let mut cursor = node.walk();
            for child in node.named_children(&mut cursor) {
                self.collect_handlers(child, source)?;
            }
        }
        Ok(())
    }

    fn collect_type_alias(
        &mut self,
        node: Node<'_>,
        snippet: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let Some(name) = declaration_name(snippet, "type") else {
            return Ok(());
        };
        let literals = stable_literals(extract_string_literals(snippet));
        if literals
            .iter()
            .any(|literal| approval_result_from_literal(literal).is_some())
        {
            self.decision_type_names.insert(name.clone());
            self.approval_unions
                .push(TypeScriptApprovalCoreApprovalUnion {
                    name,
                    literals,
                    span: TypeScriptApprovalCoreSourceSpan::from_node(node),
                });
            return Ok(());
        }
        if snippet.contains('{') && looks_approval_related(&name) {
            self.requests.push(TypeScriptApprovalCoreRequest {
                name,
                fields: fields_from_object_type(snippet, &self.decision_type_names),
                span: TypeScriptApprovalCoreSourceSpan::from_node(node),
            });
            return Ok(());
        }
        if looks_approval_related(&name) && snippet.contains("=>") {
            return Err(UnsupportedConstruct::new(
                "function type aliases are outside TypeScriptApprovalCore registrations",
                Some(node),
            ));
        }
        Ok(())
    }

    fn collect_interface(
        &mut self,
        node: Node<'_>,
        snippet: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let Some(name) = declaration_name(snippet, "interface") else {
            return Ok(());
        };
        if !looks_approval_related(&name) && !snippet.contains("Approval") {
            return Ok(());
        }
        self.requests.push(TypeScriptApprovalCoreRequest {
            name,
            fields: fields_from_object_type(snippet, &self.decision_type_names),
            span: TypeScriptApprovalCoreSourceSpan::from_node(node),
        });
        Ok(())
    }

    fn collect_policy_declaration(
        &mut self,
        node: Node<'_>,
        snippet: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let Some(name) = const_name(snippet) else {
            return Ok(());
        };
        let lower = name.to_ascii_lowercase();
        let kind = if lower.contains("block") || lower.contains("deny") || lower.contains("denied")
        {
            Some(TypeScriptApprovalCorePolicyKind::Blocklist)
        } else if lower.contains("allow")
            || lower.contains("safe")
            || lower.contains("trusted")
            || lower.contains("permitted")
        {
            Some(TypeScriptApprovalCorePolicyKind::Allowlist)
        } else {
            None
        };
        let Some(kind) = kind else {
            return Ok(());
        };
        let entries = stable_literals(extract_string_literals(snippet));
        if entries.is_empty() {
            return Ok(());
        }
        self.policies.push(TypeScriptApprovalCorePolicy {
            name,
            kind,
            entries,
            span: TypeScriptApprovalCoreSourceSpan::from_node(node),
        });
        Ok(())
    }

    fn collect_function(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let snippet = text(node, source)?;
        let Some(name) = function_name(snippet) else {
            return Ok(());
        };
        self.collect_handler_like(node, source, snippet, name)
    }

    fn collect_arrow_function(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        let snippet = text(node, source)?;
        if !snippet.contains("=>") {
            return Ok(());
        }
        let Some(name) = const_name(snippet) else {
            return Ok(());
        };
        self.collect_handler_like(node, source, snippet, name)
    }

    fn collect_handler_like(
        &mut self,
        node: Node<'_>,
        source: &str,
        snippet: &str,
        name: String,
    ) -> Result<(), UnsupportedConstruct> {
        let return_type = return_annotation(snippet).unwrap_or_default();
        let typed_approval = is_approval_type(&return_type, &self.decision_type_names);
        let boolean_policy = is_boolean_policy_handler(&name, &return_type);
        let return_literals = return_string_literals(snippet);
        let saw_approval_literal = return_literals
            .iter()
            .any(|literal| approval_result_from_literal(literal).is_some());
        if saw_approval_literal && !typed_approval {
            return Err(UnsupportedConstruct::new(
                format!(
                    "function '{name}' returns approval literals without an approval return type"
                ),
                Some(node),
            ));
        }
        if !typed_approval && !boolean_policy {
            return Ok(());
        }
        if typed_approval {
            reject_unsupported_handler_constructs(node)?;
        }

        let mut results = return_literals
            .iter()
            .filter_map(|literal| approval_result_from_literal(literal))
            .collect::<BTreeSet<_>>();
        if boolean_policy {
            results.insert(TypeScriptApprovalCoreApprovalResult::Allow);
            results.insert(TypeScriptApprovalCoreApprovalResult::Deny);
        }
        if results.is_empty() {
            return Ok(());
        }
        let default_result = if boolean_policy {
            Some(TypeScriptApprovalCoreApprovalResult::Deny)
        } else {
            return_literals
                .iter()
                .rev()
                .find_map(|literal| approval_result_from_literal(literal))
        };
        let calls = stable_strings(
            function_calls(snippet)
                .into_iter()
                .filter(|call| call != &name)
                .collect(),
        );
        let fallback_chain = calls
            .iter()
            .filter(|call| looks_fallback_related(call))
            .cloned()
            .collect::<Vec<_>>();
        let handler = TypeScriptApprovalCoreHandler {
            name: name.clone(),
            is_async: snippet.trim_start().starts_with("async ")
                || snippet.contains(" async function ")
                || snippet.contains("export async function"),
            results: results.into_iter().collect(),
            default_result,
            calls,
            fallback_chain,
            span: TypeScriptApprovalCoreSourceSpan::from_node(node),
        };
        self.handlers.insert(name.clone(), handler);
        for (surface, span) in decorator_surfaces(node, source)? {
            self.registrations.push(TypeScriptApprovalCoreRegistration {
                surface,
                handler: name.clone(),
                via_decorator: true,
                span,
            });
        }
        Ok(())
    }

    fn collect_explicit_registrations(
        &mut self,
        node: Node<'_>,
        source: &str,
    ) -> Result<(), UnsupportedConstruct> {
        collect_decorator_register_approver_calls(node, source, &mut self.registrations)?;
        collect_register_approver_calls(node, source, &mut self.registrations)
    }

    fn finish(mut self, source: &str) -> Result<TypeScriptApprovalCoreAst, UnsupportedConstruct> {
        self.registrations.sort_by(|left, right| {
            left.surface
                .cmp(&right.surface)
                .then(left.handler.cmp(&right.handler))
                .then(left.via_decorator.cmp(&right.via_decorator))
        });
        self.registrations.dedup_by(|left, right| {
            left.surface == right.surface
                && left.handler == right.handler
                && left.via_decorator == right.via_decorator
        });
        let mut ast = TypeScriptApprovalCoreAst {
            hash_algorithm: CORE_HASH_ALGORITHM.to_string(),
            canonical_hash: String::new(),
            approval_unions: sorted_by_name(self.approval_unions),
            requests: sorted_by_name(self.requests),
            policies: sorted_by_name(self.policies),
            handlers: self.handlers.into_values().collect(),
            registrations: self.registrations,
        };
        ast.canonical_hash = canonical_hash(source, &ast)?;
        Ok(ast)
    }
}

trait NamedCore {
    fn name(&self) -> &str;
}

impl NamedCore for TypeScriptApprovalCoreApprovalUnion {
    fn name(&self) -> &str {
        &self.name
    }
}
impl NamedCore for TypeScriptApprovalCoreRequest {
    fn name(&self) -> &str {
        &self.name
    }
}
impl NamedCore for TypeScriptApprovalCorePolicy {
    fn name(&self) -> &str {
        &self.name
    }
}

fn sorted_by_name<T: NamedCore>(mut values: Vec<T>) -> Vec<T> {
    values.sort_by(|left, right| left.name().cmp(right.name()));
    values
}

fn canonical_hash(
    source: &str,
    ast: &TypeScriptApprovalCoreAst,
) -> Result<String, UnsupportedConstruct> {
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

pub(crate) fn approval_result_from_literal(
    literal: &str,
) -> Option<TypeScriptApprovalCoreApprovalResult> {
    match literal {
        "allow" | "approve" | "allow-once" | "allow-always" | "allowlist" | "full" => {
            Some(TypeScriptApprovalCoreApprovalResult::Allow)
        }
        "deny" | "block" => Some(TypeScriptApprovalCoreApprovalResult::Deny),
        "ask" | "defer" | "review" => Some(TypeScriptApprovalCoreApprovalResult::Ask),
        "escalate" => Some(TypeScriptApprovalCoreApprovalResult::Escalate),
        _ => None,
    }
}

pub(crate) fn approval_result_literal(
    result: &TypeScriptApprovalCoreApprovalResult,
) -> &'static str {
    match result {
        TypeScriptApprovalCoreApprovalResult::Allow => "allow",
        TypeScriptApprovalCoreApprovalResult::Deny => "deny",
        TypeScriptApprovalCoreApprovalResult::Ask => "ask",
        TypeScriptApprovalCoreApprovalResult::Escalate => "escalate",
    }
}

fn declaration_name(snippet: &str, keyword: &str) -> Option<String> {
    let mut tokens = identifier_tokens(snippet);
    let index = tokens.iter().position(|token| token == keyword)?;
    tokens.drain(..=index);
    tokens.into_iter().next()
}

fn const_name(snippet: &str) -> Option<String> {
    let tokens = identifier_tokens(snippet);
    tokens
        .windows(2)
        .find(|window| matches!(window[0].as_str(), "const" | "let" | "var"))
        .map(|window| window[1].clone())
}

fn function_name(snippet: &str) -> Option<String> {
    let tokens = identifier_tokens(snippet);
    tokens
        .windows(2)
        .find(|window| window[0] == "function")
        .map(|window| window[1].clone())
}

fn return_annotation(snippet: &str) -> Option<String> {
    let header = snippet
        .split_once('{')
        .map(|(head, _)| head)
        .unwrap_or(snippet)
        .split_once("=>")
        .map(|(head, _)| head)
        .unwrap_or_else(|| {
            snippet
                .split_once('{')
                .map(|(head, _)| head)
                .unwrap_or(snippet)
        });
    header
        .rsplit_once("):")
        .or_else(|| header.rsplit_once(':'))
        .map(|(_, annotation)| annotation.trim().trim_end_matches(';').to_string())
}

fn is_approval_type(annotation: &str, decision_type_names: &BTreeSet<String>) -> bool {
    let tokens = identifier_tokens(annotation);
    tokens.iter().any(|token| {
        decision_type_names.contains(token)
            || token.ends_with("Approval")
            || token.ends_with("ApprovalDecision")
            || token == "ApprovalResult"
    })
}

fn is_boolean_policy_handler(name: &str, annotation: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    annotation.contains("boolean")
        && (lower.starts_with("should")
            || lower.starts_with("is")
            || lower.starts_with("has")
            || lower.contains("allow")
            || lower.contains("deny")
            || lower.contains("approval")
            || lower.contains("fallback")
            || lower.contains("failover"))
}

fn reject_unsupported_handler_constructs(node: Node<'_>) -> Result<(), UnsupportedConstruct> {
    if let Some((unsupported, unsupported_node)) = unsupported_handler_construct(node) {
        return Err(UnsupportedConstruct::new(
            format!("approval handler contains unsupported '{unsupported}'"),
            Some(unsupported_node),
        ));
    }
    Ok(())
}

fn unsupported_handler_construct(node: Node<'_>) -> Option<(&'static str, Node<'_>)> {
    let unsupported = match node.kind() {
        "switch_statement" => Some("switch"),
        "for_statement" | "for_in_statement" | "for_of_statement" => Some("for"),
        "while_statement" | "do_statement" => Some("while"),
        "try_statement" => Some("try"),
        "catch_clause" => Some("catch"),
        "throw_statement" => Some("throw"),
        _ => None,
    };
    if let Some(unsupported) = unsupported {
        return Some((unsupported, node));
    }
    let mut cursor = node.walk();
    node.named_children(&mut cursor)
        .find_map(unsupported_handler_construct)
}

fn fields_from_object_type(
    snippet: &str,
    decision_type_names: &BTreeSet<String>,
) -> Vec<TypeScriptApprovalCoreField> {
    let body = snippet
        .split_once('{')
        .and_then(|(_, rest)| rest.rsplit_once('}').map(|(body, _)| body))
        .unwrap_or("");
    body.lines()
        .filter_map(|line| {
            let line = line.trim().trim_end_matches(';').trim_end_matches(',');
            let (name, type_name) = line.split_once(':')?;
            let name = name.trim().trim_end_matches('?').to_string();
            if name.is_empty() {
                return None;
            }
            let type_name = type_name.trim().to_string();
            let approval_position = is_approval_type(&type_name, decision_type_names)
                || extract_string_literals(&type_name)
                    .iter()
                    .any(|literal| approval_result_from_literal(literal).is_some());
            Some(TypeScriptApprovalCoreField {
                name,
                type_name,
                approval_position,
            })
        })
        .collect()
}

fn return_string_literals(snippet: &str) -> Vec<String> {
    snippet
        .lines()
        .filter(|line| line.trim_start().starts_with("return "))
        .flat_map(extract_string_literals)
        .collect()
}

fn function_calls(snippet: &str) -> Vec<String> {
    let mut calls = Vec::new();
    for (index, _) in snippet.match_indices('(') {
        let head = &snippet[..index];
        let name = identifier_tokens(head).into_iter().next_back();
        if let Some(name) = name
            && !matches!(
                name.as_str(),
                "if" | "for" | "while" | "switch" | "function" | "return" | "Promise"
            )
        {
            calls.push(name);
        }
    }
    stable_strings(calls)
}

fn decorator_surfaces(
    node: Node<'_>,
    source: &str,
) -> Result<Vec<(String, TypeScriptApprovalCoreSourceSpan)>, UnsupportedConstruct> {
    let mut surfaces = Vec::new();
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        if child.kind() != "decorator" {
            continue;
        }
        if let Some(call) = register_approver_call_node(child, source)? {
            surfaces.extend(
                call.surfaces
                    .into_iter()
                    .map(|surface| (surface, call.span.clone())),
            );
        }
    }
    surfaces.sort();
    surfaces.dedup();
    Ok(surfaces)
}

fn collect_register_approver_calls(
    node: Node<'_>,
    source: &str,
    registrations: &mut Vec<TypeScriptApprovalCoreRegistration>,
) -> Result<(), UnsupportedConstruct> {
    if node.kind() == "decorator" {
        return Ok(());
    }
    if let Some(call) = register_approver_call_node(node, source)?
        && let Some(handler) = call.handler
    {
        for surface in call.surfaces {
            registrations.push(TypeScriptApprovalCoreRegistration {
                surface,
                handler: handler.clone(),
                via_decorator: false,
                span: call.span.clone(),
            });
        }
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_register_approver_calls(child, source, registrations)?;
    }
    Ok(())
}

fn collect_decorator_register_approver_calls(
    node: Node<'_>,
    source: &str,
    registrations: &mut Vec<TypeScriptApprovalCoreRegistration>,
) -> Result<(), UnsupportedConstruct> {
    let mut pending_surfaces = Vec::new();
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        if child.kind() == "decorator" {
            if let Some(call) = register_approver_call_node(child, source)? {
                pending_surfaces.extend(
                    call.surfaces
                        .into_iter()
                        .map(|surface| (surface, call.span.clone())),
                );
            }
            continue;
        }
        if !pending_surfaces.is_empty()
            && let Some(handler) = declaration_node_name(child, source)?
        {
            for (surface, span) in pending_surfaces.drain(..) {
                registrations.push(TypeScriptApprovalCoreRegistration {
                    surface,
                    handler: handler.clone(),
                    via_decorator: true,
                    span,
                });
            }
        }
        collect_decorator_register_approver_calls(child, source, registrations)?;
    }

    if !pending_surfaces.is_empty()
        && let Some(handler) = declaration_node_name(node, source)?
    {
        for (surface, span) in pending_surfaces {
            registrations.push(TypeScriptApprovalCoreRegistration {
                surface,
                handler: handler.clone(),
                via_decorator: true,
                span,
            });
        }
    }
    Ok(())
}

fn declaration_node_name(
    node: Node<'_>,
    source: &str,
) -> Result<Option<String>, UnsupportedConstruct> {
    if !matches!(
        node.kind(),
        "function_declaration"
            | "method_definition"
            | "lexical_declaration"
            | "variable_declaration"
    ) {
        return Ok(None);
    }
    let snippet = text(node, source)?;
    Ok(function_name(snippet).or_else(|| const_name(snippet)))
}

struct RegisterApproverCall {
    surfaces: Vec<String>,
    handler: Option<String>,
    span: TypeScriptApprovalCoreSourceSpan,
}

fn register_approver_call_node(
    node: Node<'_>,
    source: &str,
) -> Result<Option<RegisterApproverCall>, UnsupportedConstruct> {
    if node.kind() == "decorator" {
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if let Some(call) = register_approver_call_node(child, source)? {
                return Ok(Some(call));
            }
        }
        return Ok(None);
    }
    if node.kind() != "call_expression" {
        return Ok(None);
    }
    let Some(function) = node.child_by_field_name("function") else {
        return Ok(None);
    };
    if expression_tail_identifier(function, source)?.as_deref() != Some("registerApprover") {
        return Ok(None);
    }
    let Some(arguments) = node
        .child_by_field_name("arguments")
        .or_else(|| named_child_of_kind(node, "arguments"))
    else {
        return Ok(Some(RegisterApproverCall {
            surfaces: Vec::new(),
            handler: None,
            span: TypeScriptApprovalCoreSourceSpan::from_node(node),
        }));
    };
    let mut surfaces = Vec::new();
    let mut handler = None;
    let mut cursor = arguments.walk();
    for argument in arguments.named_children(&mut cursor) {
        if surfaces.is_empty() {
            surfaces.extend(extract_string_literals(text(argument, source)?));
            if !surfaces.is_empty() {
                continue;
            }
        }
        if handler.is_none() {
            handler = expression_tail_identifier(argument, source)?;
        }
    }
    Ok(Some(RegisterApproverCall {
        surfaces,
        handler,
        span: TypeScriptApprovalCoreSourceSpan::from_node(node),
    }))
}

fn named_child_of_kind<'tree>(node: Node<'tree>, kind: &str) -> Option<Node<'tree>> {
    let mut cursor = node.walk();
    node.named_children(&mut cursor)
        .find(|child| child.kind() == kind)
}

fn expression_tail_identifier(
    node: Node<'_>,
    source: &str,
) -> Result<Option<String>, UnsupportedConstruct> {
    if matches!(node.kind(), "identifier" | "property_identifier") {
        return Ok(Some(text(node, source)?.to_string()));
    }
    if matches!(node.kind(), "string" | "comment") {
        return Ok(None);
    }
    let mut result = None;
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        if let Some(identifier) = expression_tail_identifier(child, source)? {
            result = Some(identifier);
        }
    }
    Ok(result)
}

fn looks_approval_related(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.contains("approval")
        || lower.contains("approver")
        || lower.contains("allow")
        || lower.contains("deny")
        || lower.contains("policy")
}

fn looks_fallback_related(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.contains("fallback") || lower.contains("failover") || lower.contains("retry")
}

fn stable_literals(literals: Vec<String>) -> Vec<String> {
    stable_strings(literals)
}

fn stable_strings(mut values: Vec<String>) -> Vec<String> {
    values.sort();
    values.dedup();
    values
}

fn extract_string_literals(text: &str) -> Vec<String> {
    let mut literals = Vec::new();
    let mut quote = None;
    let mut start = 0usize;
    let mut escaped = false;
    for (index, character) in text.char_indices() {
        match (quote, character, escaped) {
            (None, '"' | '\'' | '`', _) => {
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
            if is_ecmascript_identifier_start(character) {
                current.push(character);
            }
        } else if is_ecmascript_identifier_continue(character) {
            current.push(character);
        } else if !current.is_empty() {
            tokens.push(std::mem::take(&mut current));
        }
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

fn is_ecmascript_identifier_start(character: char) -> bool {
    character == '$' || character == '_' || is_xid_start(character)
}

fn is_ecmascript_identifier_continue(character: char) -> bool {
    character == '$'
        || character == '_'
        || character == '\u{200c}'
        || character == '\u{200d}'
        || is_xid_continue(character)
}

fn text<'a>(node: Node<'_>, source: &'a str) -> Result<&'a str, UnsupportedConstruct> {
    node.utf8_text(source.as_bytes()).map_err(|error| {
        UnsupportedConstruct::new(format!("failed to read source text: {error}"), Some(node))
    })
}
