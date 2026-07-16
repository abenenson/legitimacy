use super::{
    ExtractionFileReport, ExtractionFileStatus, ExtractionSourceLanguage, ParsedFunction,
    ParsedMatchArm,
};
use crate::LegitimacyError;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
};
use tree_sitter::{Node, Parser};

pub(crate) fn parse_typescript_functions(
    source_dir: &Path,
    ts_files: &[PathBuf],
    allow_partial: bool,
    file_reports: &mut Vec<ExtractionFileReport>,
) -> Result<Vec<ParsedFunction>, LegitimacyError> {
    let mut parser = Parser::new();
    let mut functions = Vec::new();

    for path in ts_files {
        set_typescript_language(&mut parser, path)?;

        let source = match fs::read_to_string(path) {
            Ok(source) => source,
            Err(source_error) => {
                file_reports.push(ExtractionFileReport {
                    path: path
                        .strip_prefix(source_dir)
                        .unwrap_or(path.as_path())
                        .display()
                        .to_string(),
                    language: ExtractionSourceLanguage::TypeScript,
                    status: if allow_partial {
                        ExtractionFileStatus::Skipped
                    } else {
                        ExtractionFileStatus::Error
                    },
                    detail: Some(source_error.to_string()),
                });
                if allow_partial {
                    continue;
                }
                return Err(LegitimacyError::Io {
                    context: format!("TypeScript source '{}'", path.display()),
                    source: source_error,
                });
            }
        };
        let tree = match parser.parse(&source, None) {
            Some(tree) if !tree.root_node().has_error() => tree,
            Some(_) | None => {
                let message = format!("failed to parse TypeScript source '{}'", path.display());
                file_reports.push(ExtractionFileReport {
                    path: path
                        .strip_prefix(source_dir)
                        .unwrap_or(path.as_path())
                        .display()
                        .to_string(),
                    language: ExtractionSourceLanguage::TypeScript,
                    status: if allow_partial {
                        ExtractionFileStatus::Skipped
                    } else {
                        ExtractionFileStatus::Error
                    },
                    detail: Some(message.clone()),
                });
                if allow_partial {
                    continue;
                }
                return Err(LegitimacyError::invalid_input(message));
            }
        };
        let relative_path = path
            .strip_prefix(source_dir)
            .unwrap_or(path.as_path())
            .display()
            .to_string();
        let import_aliases = collect_import_aliases(tree.root_node(), &relative_path, &source)?;
        file_reports.push(ExtractionFileReport {
            path: relative_path.clone(),
            language: ExtractionSourceLanguage::TypeScript,
            status: ExtractionFileStatus::Parsed,
            detail: None,
        });

        let mut cursor = tree.root_node().walk();
        for child in tree.root_node().children(&mut cursor) {
            collect_function_items(
                child,
                &source,
                &relative_path,
                &import_aliases,
                &mut functions,
            )?;
        }
    }

    Ok(functions)
}

fn set_typescript_language(parser: &mut Parser, path: &Path) -> Result<(), LegitimacyError> {
    let extension = path
        .extension()
        .and_then(|value| value.to_str())
        .unwrap_or("");
    let language = if extension == "tsx" {
        tree_sitter_typescript::LANGUAGE_TSX
    } else {
        tree_sitter_typescript::LANGUAGE_TYPESCRIPT
    };

    parser.set_language(&language.into()).map_err(|error| {
        LegitimacyError::invalid_input(format!(
            "failed to load tree-sitter-typescript grammar for '{}': {error}",
            path.display()
        ))
    })
}

fn collect_function_items(
    node: Node<'_>,
    source: &str,
    relative_path: &str,
    import_aliases: &BTreeMap<String, String>,
    functions: &mut Vec<ParsedFunction>,
) -> Result<(), LegitimacyError> {
    if is_function_like(node) {
        functions.push(parse_function_item(
            node,
            source,
            relative_path,
            import_aliases,
        )?);
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_function_items(child, source, relative_path, import_aliases, functions)?;
    }

    Ok(())
}

fn parse_function_item(
    node: Node<'_>,
    source: &str,
    relative_path: &str,
    import_aliases: &BTreeMap<String, String>,
) -> Result<ParsedFunction, LegitimacyError> {
    let function_name = infer_function_name(node, source)?;
    let body_node = node.child_by_field_name("body").ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "TypeScript function '{}' in '{}' is missing a body",
            function_name, relative_path
        ))
    })?;

    let body_text = text(body_node, source)?.to_string();
    let mut string_literals = Vec::new();
    let mut condition_fields = BTreeSet::new();
    let mut condition_texts = Vec::new();
    let mut return_texts = Vec::new();
    let mut assignment_texts = Vec::new();
    let mut decision_branches = Vec::new();
    let mut calls = BTreeSet::new();
    let mut callback_refs = BTreeSet::new();
    let mut match_arms = Vec::new();
    let mut has_if_chain = false;

    collect_function_features(
        body_node,
        node,
        source,
        &mut string_literals,
        &mut condition_fields,
        &mut condition_texts,
        &mut return_texts,
        &mut assignment_texts,
        &mut decision_branches,
        &mut calls,
        &mut callback_refs,
        &mut match_arms,
        &mut has_if_chain,
    )?;

    Ok(ParsedFunction {
        id: format!("{relative_path}::{function_name}"),
        function_name,
        relative_path: relative_path.to_string(),
        language: ExtractionSourceLanguage::TypeScript,
        line_start: node.start_position().row + 1,
        line_end: node.end_position().row + 1,
        body_text,
        condition_fields,
        condition_texts,
        string_literals,
        return_texts,
        assignment_texts,
        decision_branches,
        import_aliases: import_aliases.clone(),
        calls,
        callback_refs,
        match_arms,
        has_if_chain,
    })
}

fn collect_import_aliases(
    root: Node<'_>,
    relative_path: &str,
    source: &str,
) -> Result<BTreeMap<String, String>, LegitimacyError> {
    let mut aliases = BTreeMap::new();
    let mut cursor = root.walk();
    for child in root.children(&mut cursor) {
        if child.kind() == "import_statement" {
            let snippet = text(child, source)?.trim();
            register_ts_import(relative_path, snippet, &mut aliases);
        }
    }

    Ok(aliases)
}

fn register_ts_import(relative_path: &str, snippet: &str, aliases: &mut BTreeMap<String, String>) {
    let Some((left, right)) = snippet.split_once(" from ") else {
        return;
    };
    let module = normalize_ts_module_specifier(
        relative_path,
        right
            .trim()
            .trim_end_matches(';')
            .trim_matches('"')
            .trim_matches('\''),
    );
    let left = left.trim_start_matches("import ").trim();

    if let Some(namespace) = left.strip_prefix("* as ") {
        aliases.insert(namespace.trim().to_ascii_lowercase(), module);
        return;
    }

    if let Some(grouped) = left
        .strip_prefix('{')
        .and_then(|value| value.strip_suffix('}'))
    {
        for entry in grouped
            .split(',')
            .map(str::trim)
            .filter(|entry| !entry.is_empty())
        {
            let (name, alias) = match entry.split_once(" as ") {
                Some((name, alias)) => (name.trim(), alias.trim()),
                None => (entry, entry),
            };
            aliases.insert(
                normalize_identifier(alias),
                format!("{module}.{}", normalize_identifier(name)),
            );
        }
    }
}

fn normalize_ts_module_specifier(relative_path: &str, specifier: &str) -> String {
    if !specifier.starts_with('.') {
        return specifier.replace('/', ".");
    }

    let base = Path::new(relative_path)
        .parent()
        .unwrap_or_else(|| Path::new(""));
    let joined = base.join(specifier);
    let mut parts = Vec::new();
    for component in joined.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                let _ = parts.pop();
            }
            Component::Normal(part) => parts.push(part.to_string_lossy().to_string()),
            Component::RootDir | Component::Prefix(_) => {}
        }
    }
    if let Some(last) = parts.last_mut() {
        for suffix in [".ts", ".tsx", ".js", ".jsx"] {
            if let Some(stripped) = last.strip_suffix(suffix) {
                *last = stripped.to_string();
            }
        }
    }
    parts.join(".")
}

#[allow(clippy::too_many_arguments)]
fn collect_function_features(
    node: Node<'_>,
    root_function: Node<'_>,
    source: &str,
    string_literals: &mut Vec<String>,
    condition_fields: &mut BTreeSet<String>,
    condition_texts: &mut Vec<String>,
    return_texts: &mut Vec<String>,
    assignment_texts: &mut Vec<String>,
    decision_branches: &mut Vec<String>,
    calls: &mut BTreeSet<String>,
    callback_refs: &mut BTreeSet<String>,
    match_arms: &mut Vec<ParsedMatchArm>,
    has_if_chain: &mut bool,
) -> Result<(), LegitimacyError> {
    if is_function_like(node) && !same_node(node, root_function) {
        return Ok(());
    }

    match node.kind() {
        "if_statement" => {
            *has_if_chain = true;
            if let Some(condition) = node.child_by_field_name("condition") {
                collect_field_candidates(condition, source, condition_fields)?;
                condition_texts.push(text(condition, source)?.to_string());
            }
            if let Some(consequence) = node.child_by_field_name("consequence") {
                decision_branches.push(text(consequence, source)?.trim().to_string());
            }
            if let Some(alternative) = node.child_by_field_name("alternative") {
                decision_branches.push(text(alternative, source)?.trim().to_string());
            }
        }
        "switch_statement" => {
            if let Some(value) = node
                .child_by_field_name("value")
                .or_else(|| node.child_by_field_name("condition"))
            {
                collect_field_candidates(value, source, condition_fields)?;
                condition_texts.push(text(value, source)?.to_string());
            }

            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "switch_body" {
                    let mut body_cursor = child.walk();
                    for case in child.children(&mut body_cursor) {
                        if matches!(case.kind(), "switch_case" | "switch_default") {
                            match_arms.push(parse_switch_arm(case, source)?);
                        }
                    }
                }
            }
        }
        "call_expression" => {
            if let Some(function) = node.child_by_field_name("function")
                && let Some(call_name) = call_target_name(function, source)?
            {
                calls.insert(call_name);
            }
            if let Some(arguments) = node.child_by_field_name("arguments") {
                let mut cursor = arguments.walk();
                for argument in arguments.named_children(&mut cursor) {
                    if is_function_like(argument) {
                        callback_refs.insert(infer_function_name(argument, source)?);
                    } else if is_identifier_kind(argument.kind()) {
                        let candidate = normalize_identifier(text(argument, source)?);
                        if is_callback_candidate(&candidate) {
                            callback_refs.insert(candidate);
                        }
                    }
                }
            }
        }
        "return_statement" => {
            let snippet = if let Some(argument) = node.child_by_field_name("argument") {
                text(argument, source)?.to_string()
            } else {
                text(node, source)?.to_string()
            };
            return_texts.push(snippet);
        }
        "variable_declarator" | "assignment_expression" => {
            assignment_texts.push(text(node, source)?.trim().to_string());
        }
        "string" | "template_string" => {
            let literal = normalize_string_literal(text(node, source)?);
            if !literal.trim().is_empty() {
                string_literals.push(literal);
            }
        }
        _ => {}
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_function_features(
            child,
            root_function,
            source,
            string_literals,
            condition_fields,
            condition_texts,
            return_texts,
            assignment_texts,
            decision_branches,
            calls,
            callback_refs,
            match_arms,
            has_if_chain,
        )?;
    }

    Ok(())
}

fn parse_switch_arm(node: Node<'_>, source: &str) -> Result<ParsedMatchArm, LegitimacyError> {
    let pattern_text = node
        .child_by_field_name("value")
        .map(|value| text(value, source))
        .transpose()?
        .unwrap_or_else(|| {
            if node.kind() == "switch_default" {
                "default"
            } else {
                ""
            }
        })
        .to_string();

    let body_text = text(node, source)?.to_string();
    let mut string_literals = Vec::new();
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_string_literals(child, source, &mut string_literals)?;
    }

    Ok(ParsedMatchArm {
        pattern_text,
        body_text,
        string_literals,
    })
}

fn collect_string_literals(
    node: Node<'_>,
    source: &str,
    string_literals: &mut Vec<String>,
) -> Result<(), LegitimacyError> {
    if matches!(node.kind(), "string" | "template_string") {
        let literal = normalize_string_literal(text(node, source)?);
        if !literal.trim().is_empty() {
            string_literals.push(literal);
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_string_literals(child, source, string_literals)?;
    }

    Ok(())
}

fn collect_field_candidates(
    node: Node<'_>,
    source: &str,
    fields: &mut BTreeSet<String>,
) -> Result<(), LegitimacyError> {
    if is_identifier_kind(node.kind()) {
        let candidate = normalize_identifier(text(node, source)?);
        if is_metric_candidate(&candidate) {
            fields.insert(candidate);
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_field_candidates(child, source, fields)?;
    }

    Ok(())
}

fn infer_function_name(node: Node<'_>, source: &str) -> Result<String, LegitimacyError> {
    if let Some(name) = node
        .child_by_field_name("name")
        .and_then(|name| identifier_text(name, source).transpose())
        .transpose()?
    {
        return Ok(name);
    }

    if let Some(parent) = node.parent() {
        match parent.kind() {
            "variable_declarator" => {
                if let Some(name) = parent
                    .child_by_field_name("name")
                    .and_then(|name| identifier_text(name, source).transpose())
                    .transpose()?
                {
                    return Ok(name);
                }
            }
            "pair" => {
                if let Some(name) = parent
                    .child_by_field_name("key")
                    .or_else(|| parent.child_by_field_name("name"))
                    .and_then(|key| identifier_text(key, source).transpose())
                    .transpose()?
                {
                    return Ok(name);
                }
            }
            "arguments" => {
                if let Some(call) = parent.parent()
                    && call.kind() == "call_expression"
                {
                    return callback_name_from_call(call, node, source);
                }
            }
            "assignment_expression" => {
                if let Some(name) = parent
                    .child_by_field_name("left")
                    .and_then(|left| call_target_name(left, source).transpose())
                    .transpose()?
                {
                    return Ok(name);
                }
            }
            _ => {}
        }
    }

    Ok(format!(
        "anonymous_callback_{}",
        node.start_position().row + 1
    ))
}

fn callback_name_from_call(
    call: Node<'_>,
    callback: Node<'_>,
    source: &str,
) -> Result<String, LegitimacyError> {
    let call_name = call
        .child_by_field_name("function")
        .map(|function| call_target_name(function, source))
        .transpose()?
        .flatten()
        .unwrap_or_else(|| "callback".to_string());
    let label = call
        .child_by_field_name("arguments")
        .and_then(|arguments| {
            let mut cursor = arguments.walk();
            arguments
                .named_children(&mut cursor)
                .find(|argument| matches!(argument.kind(), "string" | "template_string"))
        })
        .and_then(|argument| text(argument, source).ok())
        .map(|argument| normalize_identifier(&normalize_string_literal(argument)))
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| "handler".to_string());

    Ok(format!(
        "{}_{}_callback_{}",
        normalize_identifier(&call_name),
        label,
        callback.start_position().row + 1
    ))
}

fn call_target_name(node: Node<'_>, source: &str) -> Result<Option<String>, LegitimacyError> {
    if let Some(name) = identifier_text(node, source)? {
        return Ok(Some(name));
    }

    match node.kind() {
        "member_expression" => {
            let object = node
                .child_by_field_name("object")
                .or_else(|| node.child_by_field_name("argument"))
                .map(|value| call_target_name(value, source))
                .transpose()?
                .flatten();
            let property = node
                .child_by_field_name("property")
                .map(|value| identifier_text(value, source))
                .transpose()?
                .flatten();
            Ok(match (object, property) {
                (Some(object), Some(property)) => Some(format!("{object}.{property}")),
                (_, Some(property)) => Some(property),
                (Some(object), None) => Some(object),
                (None, None) => None,
            })
        }
        "subscript_expression" | "call_expression" => {
            let mut cursor = node.walk();
            let mut last_name = None;
            for child in node.children(&mut cursor) {
                if let Some(name) = identifier_text(child, source)? {
                    last_name = Some(name);
                }
            }
            Ok(last_name)
        }
        "parenthesized_expression" | "await_expression" => {
            let mut cursor = node.walk();
            for child in node.named_children(&mut cursor) {
                if let Some(name) = call_target_name(child, source)? {
                    return Ok(Some(name));
                }
            }
            Ok(None)
        }
        _ => Ok(None),
    }
}

fn identifier_text(node: Node<'_>, source: &str) -> Result<Option<String>, LegitimacyError> {
    match node.kind() {
        kind if is_identifier_kind(kind) => Ok(Some(normalize_identifier(text(node, source)?))),
        "string" | "template_string" => Ok(Some(normalize_identifier(&normalize_string_literal(
            text(node, source)?,
        )))),
        _ => Ok(None),
    }
}

fn is_function_like(node: Node<'_>) -> bool {
    matches!(
        node.kind(),
        "function_declaration"
            | "function_expression"
            | "arrow_function"
            | "generator_function_declaration"
            | "method_definition"
    )
}

fn same_node(left: Node<'_>, right: Node<'_>) -> bool {
    left.kind() == right.kind()
        && left.start_byte() == right.start_byte()
        && left.end_byte() == right.end_byte()
}

fn normalize_string_literal(raw: &str) -> String {
    raw.trim()
        .trim_matches('"')
        .trim_matches('\'')
        .trim_matches('`')
        .replace("\\\"", "\"")
        .replace("\\'", "'")
}

fn normalize_identifier(raw: &str) -> String {
    raw.trim()
        .trim_matches(|character: char| !character.is_ascii_alphanumeric() && character != '_')
        .to_ascii_lowercase()
}

fn is_identifier_kind(kind: &str) -> bool {
    matches!(
        kind,
        "identifier"
            | "property_identifier"
            | "shorthand_property_identifier"
            | "private_property_identifier"
    )
}

fn is_metric_candidate(field: &str) -> bool {
    !field.is_empty()
        && !matches!(
            field,
            "pi" | "ctx"
                | "event"
                | "args"
                | "params"
                | "undefined"
                | "null"
                | "true"
                | "false"
                | "return"
                | "const"
                | "let"
                | "var"
                | "this"
                | "type"
                | "data"
                | "value"
                | "name"
                | "label"
                | "message"
                | "reason"
                | "details"
                | "content"
        )
}

fn is_callback_candidate(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|character| character.is_ascii_alphanumeric() || character == '_')
        && !matches!(name, "undefined" | "null" | "true" | "false" | "this")
}

fn text<'a>(node: Node<'_>, source: &'a str) -> Result<&'a str, LegitimacyError> {
    node.utf8_text(source.as_bytes()).map_err(|error| {
        LegitimacyError::invalid_input(format!(
            "failed to read TypeScript syntax node text: {error}"
        ))
    })
}
