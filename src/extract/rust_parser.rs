use super::{
    ExtractionFileReport, ExtractionFileStatus, ExtractionSourceLanguage, ParsedFunction,
    ParsedMatchArm,
};
use crate::LegitimacyError;
use std::{
    collections::{BTreeSet, HashMap},
    fs,
    path::{Path, PathBuf},
};
use tree_sitter::{Node, Parser};

pub(crate) fn parse_rust_functions(
    source_dir: &Path,
    rust_files: &[PathBuf],
    allow_partial: bool,
    file_reports: &mut Vec<ExtractionFileReport>,
) -> Result<Vec<ParsedFunction>, LegitimacyError> {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_rust::LANGUAGE.into())
        .map_err(|error| {
            LegitimacyError::invalid_input(format!(
                "failed to load tree-sitter-rust grammar: {error}"
            ))
        })?;

    let mut functions = Vec::new();
    for path in rust_files {
        let source = match fs::read_to_string(path) {
            Ok(source) => source,
            Err(source_error) => {
                file_reports.push(ExtractionFileReport {
                    path: path
                        .strip_prefix(source_dir)
                        .unwrap_or(path.as_path())
                        .display()
                        .to_string(),
                    language: ExtractionSourceLanguage::Rust,
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
                    context: format!("Rust source '{}'", path.display()),
                    source: source_error,
                });
            }
        };
        let tree = match parser.parse(&source, None) {
            Some(tree) if !tree.root_node().has_error() => tree,
            Some(_) | None => {
                let message = format!("failed to parse Rust source '{}'", path.display());
                file_reports.push(ExtractionFileReport {
                    path: path
                        .strip_prefix(source_dir)
                        .unwrap_or(path.as_path())
                        .display()
                        .to_string(),
                    language: ExtractionSourceLanguage::Rust,
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
        let import_aliases = collect_import_aliases(tree.root_node(), &source)?;
        file_reports.push(ExtractionFileReport {
            path: relative_path.clone(),
            language: ExtractionSourceLanguage::Rust,
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

    uniquify_function_ids(&mut functions);
    Ok(functions)
}

fn uniquify_function_ids(functions: &mut [ParsedFunction]) {
    let counts = functions
        .iter()
        .fold(HashMap::<String, usize>::new(), |mut acc, function| {
            *acc.entry(function.id.clone()).or_insert(0) += 1;
            acc
        });

    for function in functions {
        if counts.get(&function.id).copied().unwrap_or(0) > 1 {
            function.id = format!("{}@{}", function.id, function.line_start);
        }
    }
}

fn collect_function_items(
    node: Node<'_>,
    source: &str,
    relative_path: &str,
    import_aliases: &HashMap<String, String>,
    functions: &mut Vec<ParsedFunction>,
) -> Result<(), LegitimacyError> {
    if node.kind() == "function_item" && !in_test_module(node, source) {
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
    import_aliases: &HashMap<String, String>,
) -> Result<ParsedFunction, LegitimacyError> {
    let name_node = node.child_by_field_name("name").ok_or_else(|| {
        LegitimacyError::invalid_input(format!("function in '{relative_path}' is missing a name"))
    })?;
    let function_name = text(name_node, source)?.to_string();
    let body_node = node.child_by_field_name("body").ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "function '{}' in '{relative_path}' is missing a body",
            function_name
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
        language: ExtractionSourceLanguage::Rust,
        line_start: node.start_position().row + 1,
        line_end: node.end_position().row + 1,
        body_text,
        condition_fields,
        condition_texts,
        string_literals,
        return_texts,
        assignment_texts,
        decision_branches,
        import_aliases: import_aliases
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
        calls,
        callback_refs,
        match_arms,
        has_if_chain,
    })
}

fn collect_import_aliases(
    root: Node<'_>,
    source: &str,
) -> Result<HashMap<String, String>, LegitimacyError> {
    let mut aliases = HashMap::new();
    let mut cursor = root.walk();
    for child in root.children(&mut cursor) {
        if child.kind() == "use_declaration" {
            let snippet = text(child, source)?
                .trim()
                .trim_end_matches(';')
                .trim_start_matches("use ")
                .trim();
            parse_use_snippet(snippet, &mut aliases);
        }
    }

    Ok(aliases)
}

fn parse_use_snippet(snippet: &str, aliases: &mut HashMap<String, String>) {
    if let Some((prefix, grouped)) = snippet.split_once("::{") {
        let prefix = prefix.trim();
        let grouped = grouped.trim_end_matches('}');
        for entry in grouped
            .split(',')
            .map(str::trim)
            .filter(|entry| !entry.is_empty())
        {
            let path = format!("{prefix}::{entry}");
            register_rust_import(&path, aliases);
        }
        return;
    }

    register_rust_import(snippet, aliases);
}

fn register_rust_import(path: &str, aliases: &mut HashMap<String, String>) {
    let (canonical, alias) = match path.split_once(" as ") {
        Some((canonical, alias)) => (canonical.trim(), alias.trim()),
        None => (path.trim(), path.rsplit("::").next().unwrap_or(path).trim()),
    };
    aliases.insert(alias.to_string(), canonical.to_string());
}

#[allow(clippy::too_many_arguments)]
fn collect_function_features(
    node: Node<'_>,
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
    match node.kind() {
        "if_expression" => {
            *has_if_chain = true;
            if let Some(condition) = node.child_by_field_name("condition") {
                condition_texts.push(text(condition, source)?.trim().to_string());
                collect_field_candidates(condition, source, condition_fields)?;
            }
            if let Some(consequence) = node.child_by_field_name("consequence") {
                decision_branches.push(text(consequence, source)?.trim().to_string());
            }
            if let Some(alternative) = node.child_by_field_name("alternative") {
                decision_branches.push(text(alternative, source)?.trim().to_string());
            }
        }
        "match_expression" => {
            if let Some(value) = node.child_by_field_name("value") {
                condition_texts.push(text(value, source)?.trim().to_string());
                collect_field_candidates(value, source, condition_fields)?;
            }
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "match_block" {
                    let mut block_cursor = child.walk();
                    for arm in child.children(&mut block_cursor) {
                        if arm.kind() == "match_arm" {
                            match_arms.push(parse_match_arm(arm, source)?);
                        }
                    }
                }
            }
        }
        "return_expression" => {
            return_texts.push(text(node, source)?.trim().to_string());
        }
        "let_declaration" | "assignment_expression" => {
            assignment_texts.push(text(node, source)?.trim().to_string());
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
                    if argument.kind() == "identifier" {
                        let candidate = text(argument, source)?.to_string();
                        if is_callback_candidate(&candidate) {
                            callback_refs.insert(candidate);
                        }
                    }
                }
            }
        }
        "string_literal" | "raw_string_literal" => {
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

fn parse_match_arm(node: Node<'_>, source: &str) -> Result<ParsedMatchArm, LegitimacyError> {
    let pattern = node
        .child_by_field_name("pattern")
        .map(|pattern| text(pattern, source))
        .transpose()?
        .unwrap_or_default()
        .to_string();
    let value = node
        .child_by_field_name("value")
        .map(|value| text(value, source))
        .transpose()?
        .unwrap_or_default()
        .to_string();

    let mut string_literals = Vec::new();
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_string_literals(child, source, &mut string_literals)?;
    }

    Ok(ParsedMatchArm {
        pattern_text: pattern,
        body_text: value,
        string_literals,
    })
}

fn collect_string_literals(
    node: Node<'_>,
    source: &str,
    string_literals: &mut Vec<String>,
) -> Result<(), LegitimacyError> {
    if matches!(node.kind(), "string_literal" | "raw_string_literal") {
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
        "identifier" | "field_identifier" => {
            let candidate = normalize_field_name(text(node, source)?);
            if is_metric_candidate(&candidate) {
                fields.insert(candidate);
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
        "identifier" | "field_identifier" => Ok(Some(text(node, source)?.to_string())),
        "field_expression" | "scoped_identifier" | "generic_function" => {
            let mut cursor = node.walk();
            let mut last_name = None;
            for child in node.children(&mut cursor) {
                if matches!(child.kind(), "identifier" | "field_identifier") {
                    last_name = Some(text(child, source)?.to_string());
                }
            }
            Ok(last_name)
        }
        _ => Ok(None),
    }
}

fn in_test_module(node: Node<'_>, source: &str) -> bool {
    let mut current = node.parent();
    while let Some(parent) = current {
        if parent.kind() == "mod_item"
            && parent
                .child_by_field_name("name")
                .and_then(|name| text(name, source).ok())
                .is_some_and(|name| name == "tests")
        {
            return true;
        }
        current = parent.parent();
    }

    false
}

fn normalize_string_literal(raw: &str) -> String {
    raw.trim()
        .trim_start_matches('b')
        .trim_start_matches('r')
        .trim_matches('#')
        .trim_matches('"')
        .replace("\\\"", "\"")
}

fn normalize_field_name(raw: &str) -> String {
    raw.trim().trim_matches('_').to_ascii_lowercase()
}

fn is_metric_candidate(field: &str) -> bool {
    !matches!(
        field,
        "self"
            | "super"
            | "crate"
            | "ok"
            | "err"
            | "some"
            | "none"
            | "true"
            | "false"
            | "if"
            | "else"
            | "match"
            | "let"
            | "mut"
            | "result"
            | "parsed"
            | "request"
            | "handler"
            | "handlers"
            | "entries"
            | "status"
            | "error"
            | "stdout"
            | "stderr"
            | "input_json"
            | "turn_id"
    )
}

fn is_callback_candidate(name: &str) -> bool {
    name.chars()
        .all(|character| character.is_ascii_alphanumeric() || character == '_')
        && !matches!(name, "self" | "Some" | "None" | "Ok" | "Err")
}

fn text<'a>(node: Node<'_>, source: &'a str) -> Result<&'a str, LegitimacyError> {
    node.utf8_text(source.as_bytes()).map_err(|error| {
        LegitimacyError::invalid_input(format!("failed to read Rust syntax node text: {error}"))
    })
}
