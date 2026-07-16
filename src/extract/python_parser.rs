use super::{
    ExtractionFileReport, ExtractionFileStatus, ExtractionSourceLanguage, ParsedFunction,
    ParsedMatchArm,
};
use crate::LegitimacyError;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};
use tree_sitter::{Node, Parser};

pub(crate) fn parse_python_functions(
    source_dir: &Path,
    python_files: &[PathBuf],
    allow_partial: bool,
    file_reports: &mut Vec<ExtractionFileReport>,
) -> Result<Vec<ParsedFunction>, LegitimacyError> {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_python::LANGUAGE.into())
        .map_err(|error| {
            LegitimacyError::invalid_input(format!(
                "failed to load tree-sitter-python grammar: {error}"
            ))
        })?;

    let mut functions = Vec::new();
    for path in python_files {
        let source = match fs::read_to_string(path) {
            Ok(source) => source,
            Err(source_error) => {
                let relative_path = path
                    .strip_prefix(source_dir)
                    .unwrap_or(path.as_path())
                    .display()
                    .to_string();
                file_reports.push(ExtractionFileReport {
                    path: relative_path,
                    language: ExtractionSourceLanguage::Python,
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
                    context: format!("Python source '{}'", path.display()),
                    source: source_error,
                });
            }
        };
        let tree = match parser.parse(&source, None) {
            Some(tree) if !tree.root_node().has_error() => tree,
            Some(_) | None => {
                let message = format!("failed to parse Python source '{}'", path.display());
                file_reports.push(ExtractionFileReport {
                    path: path
                        .strip_prefix(source_dir)
                        .unwrap_or(path.as_path())
                        .display()
                        .to_string(),
                    language: ExtractionSourceLanguage::Python,
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
            language: ExtractionSourceLanguage::Python,
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

fn collect_function_items(
    node: Node<'_>,
    source: &str,
    relative_path: &str,
    import_aliases: &BTreeMap<String, String>,
    functions: &mut Vec<ParsedFunction>,
) -> Result<(), LegitimacyError> {
    match node.kind() {
        "function_definition" => {
            functions.push(parse_function_item(
                node,
                source,
                relative_path,
                import_aliases,
            )?);
        }
        "class_definition" => {
            functions.push(parse_class_item(
                node,
                source,
                relative_path,
                import_aliases,
            )?);
        }
        _ => {}
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_function_items(child, source, relative_path, import_aliases, functions)?;
    }

    Ok(())
}

fn parse_class_item(
    node: Node<'_>,
    source: &str,
    relative_path: &str,
    import_aliases: &BTreeMap<String, String>,
) -> Result<ParsedFunction, LegitimacyError> {
    let name_node = node.child_by_field_name("name").ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "Python class in '{relative_path}' is missing a name"
        ))
    })?;
    let function_name = text(name_node, source)?.to_string();
    let body_node = node.child_by_field_name("body").ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "Python class '{}' in '{}' is missing a body",
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
    let mut match_arms = Vec::new();
    let mut calls = BTreeSet::new();
    let mut callback_refs = BTreeSet::new();
    let mut has_if_chain = false;

    collect_decorator_features(
        node,
        source,
        &mut string_literals,
        &mut condition_fields,
        &mut condition_texts,
        &mut calls,
    )?;

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
        &mut match_arms,
        &mut calls,
        &mut callback_refs,
        &mut has_if_chain,
    )?;

    Ok(ParsedFunction {
        id: format!("{relative_path}::{function_name}"),
        function_name,
        relative_path: relative_path.to_string(),
        language: ExtractionSourceLanguage::Python,
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

fn parse_function_item(
    node: Node<'_>,
    source: &str,
    relative_path: &str,
    import_aliases: &BTreeMap<String, String>,
) -> Result<ParsedFunction, LegitimacyError> {
    let name_node = node.child_by_field_name("name").ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "Python function in '{relative_path}' is missing a name"
        ))
    })?;
    let function_name = text(name_node, source)?.to_string();
    let body_node = node.child_by_field_name("body").ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "Python function '{}' in '{}' is missing a body",
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
    let mut match_arms = Vec::new();
    let mut calls = BTreeSet::new();
    let mut callback_refs = BTreeSet::new();
    let mut has_if_chain = false;

    collect_decorator_features(
        node,
        source,
        &mut string_literals,
        &mut condition_fields,
        &mut condition_texts,
        &mut calls,
    )?;

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
        &mut match_arms,
        &mut calls,
        &mut callback_refs,
        &mut has_if_chain,
    )?;

    Ok(ParsedFunction {
        id: format!("{relative_path}::{function_name}"),
        function_name,
        relative_path: relative_path.to_string(),
        language: ExtractionSourceLanguage::Python,
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
        match child.kind() {
            "import_statement" => {
                let snippet = text(child, source)?.trim();
                register_python_import_statement(snippet, &mut aliases);
            }
            "import_from_statement" => {
                let snippet = text(child, source)?.trim();
                register_python_from_import(relative_path, snippet, &mut aliases);
            }
            _ => {}
        }
    }

    Ok(aliases)
}

fn register_python_import_statement(snippet: &str, aliases: &mut BTreeMap<String, String>) {
    let trimmed = snippet.trim_start_matches("import ").trim();
    for entry in trimmed
        .split(',')
        .map(str::trim)
        .filter(|entry| !entry.is_empty())
    {
        let (module, alias) = match entry.split_once(" as ") {
            Some((module, alias)) => (module.trim(), alias.trim()),
            None => (entry, entry.rsplit('.').next().unwrap_or(entry).trim()),
        };
        aliases.insert(alias.to_string(), module.to_string());
    }
}

fn register_python_from_import(
    _relative_path: &str,
    snippet: &str,
    aliases: &mut BTreeMap<String, String>,
) {
    let Some(rest) = snippet.strip_prefix("from ") else {
        return;
    };
    let Some((module, imports)) = rest.split_once(" import ") else {
        return;
    };
    let module = module.trim();
    for entry in imports
        .split(',')
        .map(str::trim)
        .filter(|entry| !entry.is_empty())
    {
        let (name, alias) = match entry.split_once(" as ") {
            Some((name, alias)) => (name.trim(), alias.trim()),
            None => (entry, entry),
        };
        aliases.insert(alias.to_string(), format!("{module}.{name}"));
    }
}

fn collect_decorator_features(
    node: Node<'_>,
    source: &str,
    string_literals: &mut Vec<String>,
    condition_fields: &mut BTreeSet<String>,
    condition_texts: &mut Vec<String>,
    calls: &mut BTreeSet<String>,
) -> Result<(), LegitimacyError> {
    let Some(parent) = node.parent() else {
        return Ok(());
    };
    if parent.kind() != "decorated_definition" {
        return Ok(());
    }

    let mut cursor = parent.walk();
    for child in parent.children(&mut cursor) {
        if child.kind() != "decorator" {
            continue;
        }

        let decorator_text = text(child, source)?.trim().to_string();
        condition_texts.push(decorator_text);
        collect_field_candidates(child, source, condition_fields)?;
        collect_string_literals(child, source, string_literals)?;

        let mut decorator_cursor = child.walk();
        for decorator_child in child.children(&mut decorator_cursor) {
            if decorator_child.kind() == "call"
                && let Some(function) = decorator_child.child_by_field_name("function")
                && let Some(call_name) = call_target_name(function, source)?
            {
                calls.insert(call_name);
            }
        }
    }

    Ok(())
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
    match_arms: &mut Vec<ParsedMatchArm>,
    calls: &mut BTreeSet<String>,
    callback_refs: &mut BTreeSet<String>,
    has_if_chain: &mut bool,
) -> Result<(), LegitimacyError> {
    if node.kind() == "function_definition" && !same_node(node, root_function) {
        return Ok(());
    }

    match node.kind() {
        "match_statement" => {
            *has_if_chain = true;
            decision_branches.push(text(node, source)?.trim().to_string());
        }
        "case_clause" => {
            *has_if_chain = true;
            decision_branches.push(text(node, source)?.trim().to_string());
            match_arms.push(parse_python_match_arm(node, source)?);
        }
        "if_statement" | "elif_clause" => {
            *has_if_chain = true;
            decision_branches.push(text(node, source)?.trim().to_string());
            if let Some(condition) = node.child_by_field_name("condition") {
                collect_field_candidates(condition, source, condition_fields)?;
                condition_texts.push(text(condition, source)?.trim().to_string());
            }
            if let Some(consequence) = node.child_by_field_name("consequence") {
                decision_branches.push(text(consequence, source)?.trim().to_string());
            }
            if let Some(alternative) = node.child_by_field_name("alternative") {
                decision_branches.push(text(alternative, source)?.trim().to_string());
            }
        }
        "else_clause" => {
            decision_branches.push(text(node, source)?.trim().to_string());
        }
        "return_statement" => {
            return_texts.push(text(node, source)?.trim().to_string());
        }
        "assignment" | "augmented_assignment" => {
            assignment_texts.push(text(node, source)?.trim().to_string());
        }
        "call" => {
            if let Some(function) = node.child_by_field_name("function")
                && let Some(call_name) = call_target_name(function, source)?
            {
                calls.insert(call_name);
            }
            if let Some(arguments) = node.child_by_field_name("arguments") {
                let mut cursor = arguments.walk();
                for argument in arguments.named_children(&mut cursor) {
                    if argument.kind() == "lambda" {
                        callback_refs.insert(format!(
                            "lambda_callback_{}",
                            argument.start_position().row + 1
                        ));
                    } else if argument.kind() == "identifier" {
                        let candidate = normalize_identifier(text(argument, source)?);
                        if is_callback_candidate(&candidate) {
                            callback_refs.insert(candidate);
                        }
                    }
                }
            }
        }
        "string" => {
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
            match_arms,
            calls,
            callback_refs,
            has_if_chain,
        )?;
    }

    Ok(())
}

fn parse_python_match_arm(node: Node<'_>, source: &str) -> Result<ParsedMatchArm, LegitimacyError> {
    let pattern = node
        .child_by_field_name("pattern")
        .map(|pattern| text(pattern, source))
        .transpose()?
        .unwrap_or_default()
        .trim()
        .to_string();
    let body = node
        .child_by_field_name("consequence")
        .or_else(|| node.child_by_field_name("body"))
        .map(|body| text(body, source))
        .transpose()?
        .unwrap_or_default()
        .trim()
        .to_string();
    let mut string_literals = Vec::new();
    collect_string_literals(node, source, &mut string_literals)?;

    Ok(ParsedMatchArm {
        pattern_text: pattern,
        body_text: body,
        string_literals,
    })
}

fn collect_string_literals(
    node: Node<'_>,
    source: &str,
    string_literals: &mut Vec<String>,
) -> Result<(), LegitimacyError> {
    if node.kind() == "string" {
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
    match node.kind() {
        "identifier" => {
            let candidate = normalize_identifier(text(node, source)?);
            if is_metric_candidate(&candidate) {
                fields.insert(candidate);
            }
        }
        "attribute" => {
            if let Some(attribute) = node.child_by_field_name("attribute") {
                let candidate = normalize_identifier(text(attribute, source)?);
                if is_metric_candidate(&candidate) {
                    fields.insert(candidate);
                }
            }
        }
        _ => {}
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_field_candidates(child, source, fields)?;
    }

    Ok(())
}

fn call_target_name(node: Node<'_>, source: &str) -> Result<Option<String>, LegitimacyError> {
    match node.kind() {
        "identifier" => Ok(Some(normalize_identifier(text(node, source)?))),
        "attribute" => {
            let value = node
                .child_by_field_name("object")
                .or_else(|| node.child_by_field_name("value"))
                .map(|value| call_target_name(value, source))
                .transpose()?
                .flatten();
            if let Some(attribute) = node.child_by_field_name("attribute") {
                let attribute = normalize_identifier(text(attribute, source)?);
                return Ok(Some(match value {
                    Some(value) => format!("{value}.{attribute}"),
                    None => attribute,
                }));
            }
            Ok(None)
        }
        "call" => {
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

fn same_node(left: Node<'_>, right: Node<'_>) -> bool {
    left.kind() == right.kind()
        && left.start_byte() == right.start_byte()
        && left.end_byte() == right.end_byte()
}

fn normalize_string_literal(raw: &str) -> String {
    raw.trim()
        .trim_matches('"')
        .trim_matches('\'')
        .replace("\\\"", "\"")
        .replace("\\'", "'")
}

fn normalize_identifier(raw: &str) -> String {
    raw.trim()
        .trim_matches(|character: char| !character.is_ascii_alphanumeric() && character != '_')
        .to_ascii_lowercase()
}

fn is_metric_candidate(field: &str) -> bool {
    !field.is_empty()
        && !matches!(
            field,
            "self"
                | "cls"
                | "true"
                | "false"
                | "none"
                | "and"
                | "or"
                | "not"
                | "if"
                | "else"
                | "elif"
                | "return"
                | "def"
                | "lambda"
                | "args"
                | "kwargs"
                | "request"
                | "response"
                | "user"
                | "value"
        )
}

fn is_callback_candidate(name: &str) -> bool {
    name.chars()
        .all(|character| character.is_ascii_alphanumeric() || character == '_')
        && !matches!(name, "self" | "cls" | "none" | "true" | "false")
}

fn text<'a>(node: Node<'_>, source: &'a str) -> Result<&'a str, LegitimacyError> {
    node.utf8_text(source.as_bytes()).map_err(|error| {
        LegitimacyError::invalid_input(format!("failed to read Python syntax node text: {error}"))
    })
}
