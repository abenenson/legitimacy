use super::*;

pub(super) fn collect_inventory(directory: &Path, root: &Path) -> (Vec<String>, Vec<String>) {
    let mut files = Vec::new();
    let mut directories = Vec::new();
    collect(directory, root, &mut files, &mut directories);
    files.sort();
    directories.sort();
    (files, directories)
}

pub(super) fn collect(
    directory: &Path,
    root: &Path,
    files: &mut Vec<String>,
    directories: &mut Vec<String>,
) {
    for entry in std::fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            directories.push(relative(root, &path));
            collect(&path, root, files, directories);
        } else if path.extension().and_then(|value| value.to_str()) == Some("rs") {
            files.push(relative(root, &path));
        }
    }
}

pub(super) fn classify_inventory(
    actual: &[String],
    expected: &BTreeSet<String>,
) -> Result<(), &'static str> {
    let mut seen = BTreeSet::new();
    for path in actual {
        if !expected.contains(path) {
            return Err("unregistered");
        }
        if !seen.insert(path.clone()) {
            return Err("duplicate");
        }
    }
    if &seen != expected {
        return Err("omitted");
    }
    Ok(())
}

pub(super) fn classify_directories(directories: &[String]) -> Result<(), &'static str> {
    if directories.is_empty() {
        Ok(())
    } else {
        Err("subdirectory")
    }
}

pub(super) fn classify_normative_rust_bindings(
    actual: &[String],
    expected: &BTreeSet<String>,
) -> Result<(), &'static str> {
    let mut seen = BTreeSet::new();
    for path in actual {
        if rust_path_is_test_only(path) {
            return Err("test-only");
        }
        if !expected.contains(path) {
            return Err("unregistered");
        }
        if !seen.insert(path.clone()) {
            return Err("duplicate");
        }
    }
    if &seen != expected {
        return Err("omitted");
    }
    Ok(())
}

pub(super) fn classify_relevant_rust_inventory(
    actual: &[String],
    production: &BTreeSet<String>,
    test_only: &BTreeSet<String>,
) -> Result<(), &'static str> {
    if !production.is_disjoint(test_only) {
        return Err("overlap");
    }
    let expected = production
        .union(test_only)
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut seen = BTreeSet::new();
    for path in actual {
        if !expected.contains(path) {
            return Err("unclassified");
        }
        if !seen.insert(path.clone()) {
            return Err("duplicate");
        }
    }
    if seen != expected {
        return Err("omitted");
    }
    Ok(())
}

pub(super) fn rust_path_is_test_only(path: &str) -> bool {
    path.ends_with(".rs")
        && (path.starts_with("tests/") || path.ends_with("_tests.rs") || path.contains("/tests/"))
}

pub(super) fn relevant_package_rust_candidate(path: &str) -> bool {
    path == "cli/trajectory.rs"
        || path == "tests/codex_exec_v0.rs"
        || path == "tests/codex_process_capture_cli_v0.rs"
        || path.starts_with("cli/trajectory/")
        || path.starts_with("src/trajectory/codex_exec_v0/")
        || path.starts_with("tests/codex_exec_v0/")
}

pub(super) fn classify_relevant_package_candidates(
    package_files: &[&str],
    expected: &BTreeSet<String>,
) -> Result<(), &'static str> {
    let normalized = package_files
        .iter()
        .map(|path| normalize_package_path(path))
        .collect::<Result<Vec<_>, _>>()?;
    let candidates = normalized
        .into_iter()
        .filter(|path| path.ends_with(".rs") && relevant_package_rust_candidate(path))
        .collect::<Vec<_>>();
    classify_inventory(&candidates, expected)
}

pub(super) fn normalize_package_path(path: &str) -> Result<String, &'static str> {
    if path.is_empty() || path.contains('\\') {
        return Err("noncanonical");
    }
    let normalized = Path::new(path)
        .components()
        .map(|component| match component {
            std::path::Component::Normal(component) => {
                component.to_str().map(str::to_owned).ok_or("noncanonical")
            }
            _ => Err("noncanonical"),
        })
        .collect::<Result<Vec<_>, _>>()?
        .join("/");
    if normalized != path {
        return Err("noncanonical");
    }
    Ok(normalized)
}

pub(super) fn package_path_is_generated(path: &str) -> bool {
    path.starts_with("target/")
        || path.starts_with(".git/")
        || path.ends_with(".profraw")
        || path.ends_with(".gcda")
}

pub(super) fn package_path_is_private_output(path: &str) -> bool {
    let file = path.rsplit('/').next().unwrap_or(path);
    file == "private-lineage.bin"
        || file.ends_with(".private.jsonl")
        || file.ends_with(".private.bin")
}

pub(super) fn package_path_is_owner_only_output(path: &str) -> bool {
    let file = path.rsplit('/').next().unwrap_or(path);
    file == "owner-private-lineage-sidecar.bin"
        || file.starts_with("owner-only-")
        || file.ends_with(".owner-only")
}

pub(super) fn package_path_is_named_temporary(path: &str) -> bool {
    path.rsplit('/')
        .next()
        .is_some_and(|file| file.starts_with(".legitimacy-tmp-"))
}

pub(super) fn rust_parser() -> tree_sitter::Parser {
    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(&tree_sitter_rust::LANGUAGE.into())
        .unwrap();
    parser
}

pub(super) fn named_nodes_containing<'tree>(
    node: tree_sitter::Node<'tree>,
    source: &[u8],
    kind: &str,
    needle: &str,
) -> Vec<tree_sitter::Node<'tree>> {
    let mut found = Vec::new();
    if node.kind() == kind && node.utf8_text(source).unwrap().contains(needle) {
        found.push(node);
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        found.extend(named_nodes_containing(child, source, kind, needle));
    }
    found
}

pub(super) fn direct_call_paths(
    node: tree_sitter::Node<'_>,
    source: &[u8],
) -> BTreeMap<String, usize> {
    let mut paths = BTreeMap::new();
    collect_direct_call_paths(node, source, &mut paths);
    paths
}

pub(super) fn collect_direct_call_paths(
    node: tree_sitter::Node<'_>,
    source: &[u8],
    paths: &mut BTreeMap<String, usize>,
) {
    if node.kind() == "call_expression" {
        let callee = node.child_by_field_name("function").unwrap();
        if matches!(callee.kind(), "identifier" | "scoped_identifier") {
            *paths
                .entry(callee.utf8_text(source).unwrap().to_string())
                .or_default() += 1;
        }
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_direct_call_paths(child, source, paths);
    }
}
