use super::{ExtractionSourceLanguage, SourceLanguage, collect_source_files};
use crate::{GovernanceGraph, LegitimacyError};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{fs, path::Path};
use tree_sitter::{Node, Parser, Tree};

pub const AST_HASH_SCHEMA_VERSION: &str = "legitimacy.ast-theorem-witness.v1";
pub const AST_HASH_ALGORITHM: &str = "tree-sitter-canonical-shape-and-tokens-sha256:v2";
pub const GRAPH_HASH_ALGORITHM: &str = "serde-json-pretty-sha256:v1";

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct AstHashFile {
    pub path: String,
    pub language: ExtractionSourceLanguage,
    pub ast_hash: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct AstTheoremWitness {
    pub schema_version: String,
    pub theorem_name: String,
    pub source_dir: String,
    pub ast_hash_algorithm: String,
    pub source_ast_hash: String,
    pub graph_hash_algorithm: String,
    pub governance_graph_hash: String,
    pub lean_binding_type: String,
    pub files: Vec<AstHashFile>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct AstWitnessVerification {
    pub witness_valid: bool,
    pub theorem_name: String,
    pub expected_source_ast_hash: String,
    pub actual_source_ast_hash: String,
    pub expected_governance_graph_hash: String,
    pub actual_governance_graph_hash: String,
}

struct ParsedAstFile {
    path: String,
    language: ExtractionSourceLanguage,
    canonical_sexp: String,
    canonical_tokens: String,
}

pub fn canonical_ast_fingerprint(
    source_dir: &Path,
) -> Result<(String, Vec<AstHashFile>), LegitimacyError> {
    let parsed = parse_ast_files(source_dir)?;
    let mut hasher = Sha256::new();
    hasher.update(AST_HASH_ALGORITHM.as_bytes());
    hasher.update([0]);

    let files = parsed
        .iter()
        .map(|file| {
            let file_hash = ast_file_hash(file);
            hasher.update(file.path.as_bytes());
            hasher.update([0]);
            hasher.update(language_label(&file.language).as_bytes());
            hasher.update([0]);
            hasher.update(b"shape");
            hasher.update([0]);
            hasher.update(file.canonical_sexp.as_bytes());
            hasher.update([0]);
            hasher.update(b"tokens");
            hasher.update([0]);
            hasher.update(file.canonical_tokens.as_bytes());
            hasher.update([0]);

            AstHashFile {
                path: file.path.clone(),
                language: file.language.clone(),
                ast_hash: file_hash,
            }
        })
        .collect::<Vec<_>>();

    let digest = hasher.finalize();
    Ok((sha256_label(&digest), files))
}

pub fn ast_theorem_witness(
    source_dir: &Path,
    graph: &GovernanceGraph,
    theorem_name: &str,
) -> Result<AstTheoremWitness, LegitimacyError> {
    let theorem_name = theorem_name.trim();
    if theorem_name.is_empty() {
        return Err(LegitimacyError::invalid_input(
            "AST theorem witness requires a non-empty Lean theorem name",
        ));
    }

    let (source_ast_hash, files) = canonical_ast_fingerprint(source_dir)?;
    Ok(AstTheoremWitness {
        schema_version: AST_HASH_SCHEMA_VERSION.to_string(),
        theorem_name: theorem_name.to_string(),
        source_dir: source_dir.display().to_string(),
        ast_hash_algorithm: AST_HASH_ALGORITHM.to_string(),
        source_ast_hash,
        graph_hash_algorithm: GRAPH_HASH_ALGORITHM.to_string(),
        governance_graph_hash: governance_graph_hash(graph)?,
        lean_binding_type: "Legitimacy.ASTTheoremWitnessBinding".to_string(),
        files,
    })
}

pub fn verify_ast_theorem_witness(
    witness: &AstTheoremWitness,
    source_dir: &Path,
    graph: &GovernanceGraph,
) -> Result<AstWitnessVerification, LegitimacyError> {
    if witness.schema_version != AST_HASH_SCHEMA_VERSION {
        return Err(LegitimacyError::invalid_input(format!(
            "unsupported AST theorem witness schema '{}'",
            witness.schema_version
        )));
    }
    if witness.ast_hash_algorithm != AST_HASH_ALGORITHM {
        return Err(LegitimacyError::invalid_input(format!(
            "unsupported AST hash algorithm '{}'",
            witness.ast_hash_algorithm
        )));
    }
    if witness.graph_hash_algorithm != GRAPH_HASH_ALGORITHM {
        return Err(LegitimacyError::invalid_input(format!(
            "unsupported governance graph hash algorithm '{}'",
            witness.graph_hash_algorithm
        )));
    }

    let (actual_source_ast_hash, _) = canonical_ast_fingerprint(source_dir)?;
    let actual_governance_graph_hash = governance_graph_hash(graph)?;
    let witness_valid = witness.source_ast_hash == actual_source_ast_hash
        && witness.governance_graph_hash == actual_governance_graph_hash;

    Ok(AstWitnessVerification {
        witness_valid,
        theorem_name: witness.theorem_name.clone(),
        expected_source_ast_hash: witness.source_ast_hash.clone(),
        actual_source_ast_hash,
        expected_governance_graph_hash: witness.governance_graph_hash.clone(),
        actual_governance_graph_hash,
    })
}

pub fn governance_graph_hash(graph: &GovernanceGraph) -> Result<String, LegitimacyError> {
    let bytes = serde_json::to_vec_pretty(graph).map_err(|source| LegitimacyError::Serialize {
        context: "canonical governance graph hash".to_string(),
        source,
    })?;
    let digest = Sha256::digest(bytes);
    Ok(sha256_label(&digest))
}

fn parse_ast_files(source_dir: &Path) -> Result<Vec<ParsedAstFile>, LegitimacyError> {
    let source_files = collect_source_files(source_dir)?;
    let mut parsed = Vec::with_capacity(source_files.len());
    for (path, language) in source_files {
        let source = fs::read_to_string(&path).map_err(|source| LegitimacyError::Io {
            context: format!("AST witness source '{}'", path.display()),
            source,
        })?;
        let tree = parse_tree(&path, language, &source)?;
        let relative_path = path
            .strip_prefix(source_dir)
            .unwrap_or(path.as_path())
            .to_string_lossy()
            .replace('\\', "/");
        parsed.push(ParsedAstFile {
            path: relative_path,
            language: language.into(),
            canonical_sexp: canonical_shape_sexp(tree.root_node()),
            canonical_tokens: canonical_token_stream(&tree, &source),
        });
    }

    Ok(parsed)
}

fn parse_tree(
    path: &Path,
    language: SourceLanguage,
    source: &str,
) -> Result<Tree, LegitimacyError> {
    let mut parser = Parser::new();
    match language {
        SourceLanguage::Python => parser.set_language(&tree_sitter_python::LANGUAGE.into()),
        SourceLanguage::Rust => parser.set_language(&tree_sitter_rust::LANGUAGE.into()),
        SourceLanguage::TypeScript => {
            let extension = path
                .extension()
                .and_then(|value| value.to_str())
                .unwrap_or("");
            let language = if extension == "tsx" {
                tree_sitter_typescript::LANGUAGE_TSX
            } else {
                tree_sitter_typescript::LANGUAGE_TYPESCRIPT
            };
            parser.set_language(&language.into())
        }
    }
    .map_err(|error| {
        LegitimacyError::invalid_input(format!(
            "failed to load tree-sitter grammar for AST witness '{}': {error}",
            path.display()
        ))
    })?;

    match parser.parse(source, None) {
        Some(tree) if !tree.root_node().has_error() => Ok(tree),
        Some(_) | None => Err(LegitimacyError::invalid_input(format!(
            "failed to parse source for AST witness '{}'",
            path.display()
        ))),
    }
}

fn ast_file_hash(file: &ParsedAstFile) -> String {
    let mut hasher = Sha256::new();
    hasher.update(AST_HASH_ALGORITHM.as_bytes());
    hasher.update([0]);
    hasher.update(file.path.as_bytes());
    hasher.update([0]);
    hasher.update(language_label(&file.language).as_bytes());
    hasher.update([0]);
    hasher.update(b"shape");
    hasher.update([0]);
    hasher.update(file.canonical_sexp.as_bytes());
    hasher.update([0]);
    hasher.update(b"tokens");
    hasher.update([0]);
    hasher.update(file.canonical_tokens.as_bytes());
    let digest = hasher.finalize();
    sha256_label(&digest)
}

fn canonical_shape_sexp(node: Node<'_>) -> String {
    canonical_shape_sexp_opt(node).unwrap_or_default()
}

fn canonical_shape_sexp_opt(node: Node<'_>) -> Option<String> {
    if is_comment_node(node.kind()) {
        return None;
    }

    if node.child_count() == 0 {
        return Some(node.kind().to_string());
    }

    let mut cursor = node.walk();
    let children = node
        .children(&mut cursor)
        .filter_map(canonical_shape_sexp_opt)
        .collect::<Vec<_>>();
    if children.is_empty() {
        Some(node.kind().to_string())
    } else {
        Some(format!("({} {})", node.kind(), children.join(" ")))
    }
}

fn canonical_token_stream(tree: &Tree, source: &str) -> String {
    let mut tokens = Vec::new();
    collect_leaf_tokens(tree.root_node(), source.as_bytes(), &mut tokens);
    tokens.join("\n")
}

fn collect_leaf_tokens(node: Node<'_>, source: &[u8], tokens: &mut Vec<String>) {
    if node.child_count() == 0 {
        if should_bind_leaf_token(node.kind()) {
            let text = String::from_utf8_lossy(&source[node.byte_range()]);
            tokens.push(format!("{}:{}", node.kind(), escape_token_text(&text)));
        }
        return;
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_leaf_tokens(child, source, tokens);
    }
}

fn should_bind_leaf_token(kind: &str) -> bool {
    !is_comment_node(kind)
}

fn is_comment_node(kind: &str) -> bool {
    kind.to_ascii_lowercase().contains("comment")
}

fn escape_token_text(text: &str) -> String {
    text.chars().flat_map(char::escape_default).collect()
}

fn language_label(language: &ExtractionSourceLanguage) -> &'static str {
    match language {
        ExtractionSourceLanguage::Python => "python",
        ExtractionSourceLanguage::Rust => "rust",
        ExtractionSourceLanguage::TypeScript => "typescript",
    }
}

fn sha256_label(bytes: &[u8]) -> String {
    format!(
        "sha256:{}",
        bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    )
}
