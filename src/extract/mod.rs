pub mod ast_hash;
pub(crate) mod audit;
mod boundary;
mod codex_observed_runtime;
mod corpus_pack;
pub mod kernelization;
mod pattern_support;
mod patterns;
mod python_hook_core_graph;
mod python_hook_core_parser;
mod python_parser;
mod review;
mod rust_hook_core_graph;
mod rust_hook_core_parser;
mod rust_parser;
pub mod schedule_witness;
pub mod spectral;
#[cfg(test)]
mod tests;
mod ts_parser;
mod typescript_approval_core_graph;
mod typescript_approval_core_parser;

pub use ast_hash::{
    AstHashFile, AstTheoremWitness, AstWitnessVerification, ast_theorem_witness,
    canonical_ast_fingerprint, verify_ast_theorem_witness,
};
#[cfg(test)]
pub(crate) use audit::analyze_graph;
pub use audit::{
    ExtractionAxiomResult, ExtractionCycleFinding, ExtractionParadoxResult,
    ProtocolStateAssessment, RecommendedSacrifice, analyze_extraction,
    analyze_extraction_with_review, audit_extracted_graph, audit_extracted_graph_with_review,
    audit_governance_graph, synthetic_claims,
};
pub use boundary::{BoundaryCausalSafetyAssessment, UngovernedDependency};
pub use codex_observed_runtime::{
    build_codex_oss_story_corpus_pack, import_codex_oss_story_corpus_pack,
};
pub use corpus_pack::{
    OBSERVED_RUNTIME_CLAIMS_FILENAME, OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION,
    OBSERVED_RUNTIME_MANIFEST_FILENAME, ObservedRuntimeClaimRecord, ObservedRuntimeCorpusManifest,
    ObservedRuntimeCorpusPack, ObservedRuntimeRedactionMetadata, load_observed_runtime_corpus_pack,
    observed_runtime_claims_path, observed_runtime_manifest_path,
    write_observed_runtime_corpus_pack,
};
pub use python_hook_core_parser::{
    PythonHookCoreAst, PythonHookCoreCallback, PythonHookCoreDecision, PythonHookCoreDispatchEnum,
    PythonHookCoreField, PythonHookCoreLiteralUnion, PythonHookCoreRegistration,
    PythonHookCoreSchema, PythonHookCoreSchemaKind, UnsupportedConstruct, parse_python_hook_core,
};
pub use review::{
    AliasHintOverlay, ExtractionEvidenceTier, ExtractionReviewOverlay, ReviewedEdgeOverlay,
    ReviewedNodeOverlay,
};
pub use rust_hook_core_graph::build_governance_graph as build_rust_hook_core_governance_graph;
pub use rust_hook_core_parser::{
    RustHookCoreAst, RustHookCoreDecision, RustHookCoreDecisionEnum, RustHookCoreEventDecision,
    RustHookCoreHook, RustHookCoreRegistration, RustHookCoreRegistrationKind,
    RustHookCoreUnsupportedConstruct, parse_rust_hook_core,
};
pub use typescript_approval_core_parser::{
    TypeScriptApprovalCoreApprovalResult, TypeScriptApprovalCoreApprovalUnion,
    TypeScriptApprovalCoreAst, TypeScriptApprovalCoreField, TypeScriptApprovalCoreHandler,
    TypeScriptApprovalCorePolicy, TypeScriptApprovalCorePolicyKind,
    TypeScriptApprovalCoreRegistration, TypeScriptApprovalCoreRequest,
    UnsupportedConstruct as TypeScriptApprovalCoreUnsupportedConstruct,
    parse_typescript_approval_core,
};

use crate::factor::GovernanceFactorExposure;
use crate::{GovernanceClaim, GovernanceGraph, LegitimacyError};
use boundary::assess_boundary_causal_safety;
use serde::{Deserialize, Serialize};
use spectral::SpectralAnalysis;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

#[derive(Clone, Copy, Debug, Default, Serialize, PartialEq, Eq)]
pub struct ExtractionOptions {
    pub allow_partial: bool,
    pub mode: ExtractionMode,
}

#[derive(Clone, Copy, Debug, Default, Serialize, PartialEq, Eq)]
pub enum ExtractionMode {
    #[default]
    Heuristic,
    TheoremBacked,
}

#[derive(Clone, Debug)]
pub(crate) struct ParsedMatchArm {
    pub(crate) pattern_text: String,
    pub(crate) body_text: String,
    pub(crate) string_literals: Vec<String>,
}

#[derive(Clone, Debug)]
pub(crate) struct ParsedFunction {
    pub(crate) id: String,
    pub(crate) function_name: String,
    pub(crate) relative_path: String,
    pub(crate) language: ExtractionSourceLanguage,
    pub(crate) line_start: usize,
    pub(crate) line_end: usize,
    pub(crate) body_text: String,
    pub(crate) condition_fields: BTreeSet<String>,
    pub(crate) condition_texts: Vec<String>,
    pub(crate) string_literals: Vec<String>,
    pub(crate) return_texts: Vec<String>,
    pub(crate) assignment_texts: Vec<String>,
    pub(crate) decision_branches: Vec<String>,
    pub(crate) import_aliases: BTreeMap<String, String>,
    pub(crate) calls: BTreeSet<String>,
    pub(crate) callback_refs: BTreeSet<String>,
    pub(crate) match_arms: Vec<ParsedMatchArm>,
    pub(crate) has_if_chain: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SourceLanguage {
    Python,
    Rust,
    TypeScript,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum ExtractionSourceLanguage {
    Python,
    Rust,
    TypeScript,
}

impl From<SourceLanguage> for ExtractionSourceLanguage {
    fn from(value: SourceLanguage) -> Self {
        match value {
            SourceLanguage::Python => Self::Python,
            SourceLanguage::Rust => Self::Rust,
            SourceLanguage::TypeScript => Self::TypeScript,
        }
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub enum ExtractionFileStatus {
    Parsed,
    Skipped,
    Error,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ExtractionFileReport {
    pub path: String,
    pub language: ExtractionSourceLanguage,
    pub status: ExtractionFileStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ExtractionCoverageReport {
    pub files_discovered: usize,
    pub files_parsed: usize,
    pub files_skipped: usize,
    pub files_errored: usize,
    pub complete: bool,
    pub files: Vec<ExtractionFileReport>,
}

impl ExtractionCoverageReport {
    fn from_files(files: Vec<ExtractionFileReport>) -> Self {
        let files_discovered = files.len();
        let files_parsed = files
            .iter()
            .filter(|entry| entry.status == ExtractionFileStatus::Parsed)
            .count();
        let files_skipped = files
            .iter()
            .filter(|entry| entry.status == ExtractionFileStatus::Skipped)
            .count();
        let files_errored = files
            .iter()
            .filter(|entry| entry.status == ExtractionFileStatus::Error)
            .count();

        Self {
            files_discovered,
            files_parsed,
            files_skipped,
            files_errored,
            complete: files_skipped == 0 && files_errored == 0,
            files,
        }
    }
}

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum RecognitionConfidence {
    Low,
    Medium,
    High,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct RecognizedNodeProvenance {
    pub node_id: String,
    pub function_name: String,
    pub relative_path: String,
    pub language: ExtractionSourceLanguage,
    pub line_start: usize,
    pub line_end: usize,
    pub confidence: RecognitionConfidence,
    pub tier: ExtractionEvidenceTier,
    pub rationale: Vec<String>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub enum EdgeResolutionKind {
    SameFile,
    GlobalUnique,
    ImportAlias,
    ReviewOverlay,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct RecognizedEdgeProvenance {
    pub from: String,
    pub to: String,
    pub target_symbol: String,
    pub resolution: EdgeResolutionKind,
    pub tier: ExtractionEvidenceTier,
    pub review_note: Option<String>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub enum ResolutionIssueKind {
    Unresolved,
    Ambiguous,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ResolutionIssue {
    pub caller: String,
    pub target_symbol: String,
    pub kind: ResolutionIssueKind,
    pub candidates: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct GovernanceExtractionArtifacts {
    pub source_dir: String,
    pub graph: GovernanceGraph,
    pub coverage: ExtractionCoverageReport,
    pub recognized_nodes: Vec<RecognizedNodeProvenance>,
    pub recognized_edges: Vec<RecognizedEdgeProvenance>,
    pub resolution_issues: Vec<ResolutionIssue>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub review_overlay: Option<String>,
    pub boundary_causal_safety: BoundaryCausalSafetyAssessment,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub enum ClaimCorpusProvenance {
    SyntheticStructuralProbe,
    UserSupplied,
    Fixture,
    ObservedRuntime,
    ReviewedReconstruction,
}

#[derive(Debug, Clone, Serialize)]
pub struct GovernanceAuditReport {
    pub corpus_provenance: ClaimCorpusProvenance,
    pub claims: Vec<GovernanceClaim>,
    pub cycles: Vec<ExtractionCycleFinding>,
    pub axiom_results: Vec<ExtractionAxiomResult>,
    pub paradox_results: Vec<ExtractionParadoxResult>,
    pub spectral: Option<SpectralAnalysis>,
    pub factor_exposure: GovernanceFactorExposure,
    pub protocol_assessment: ProtocolStateAssessment,
}

#[derive(Debug, Clone, Serialize)]
pub struct GovernanceExtractionReport {
    pub artifacts: GovernanceExtractionArtifacts,
    pub audit: GovernanceAuditReport,
}

struct ParsedGovernanceSources {
    functions: Vec<ParsedFunction>,
    coverage: ExtractionCoverageReport,
}

pub fn extract_governance(source_dir: &Path) -> Result<GovernanceGraph, LegitimacyError> {
    Ok(extract_governance_artifacts(source_dir, ExtractionOptions::default())?.graph)
}

fn parse_governance_sources(
    source_dir: &Path,
    options: ExtractionOptions,
) -> Result<ParsedGovernanceSources, LegitimacyError> {
    let source_files = collect_source_files(source_dir)?;
    if source_files.is_empty() {
        return Err(LegitimacyError::invalid_input(format!(
            "no supported source files were discovered under '{}'",
            source_dir.display()
        )));
    }

    let rust_files = source_files
        .iter()
        .filter(|(_, language)| *language == SourceLanguage::Rust)
        .map(|(path, _)| path.clone())
        .collect::<Vec<_>>();
    let python_files = source_files
        .iter()
        .filter(|(_, language)| *language == SourceLanguage::Python)
        .map(|(path, _)| path.clone())
        .collect::<Vec<_>>();
    let ts_files = source_files
        .iter()
        .filter(|(_, language)| *language == SourceLanguage::TypeScript)
        .map(|(path, _)| path.clone())
        .collect::<Vec<_>>();

    let mut parsed = Vec::new();
    let mut file_reports = Vec::new();
    if !rust_files.is_empty() {
        parsed.extend(rust_parser::parse_rust_functions(
            source_dir,
            &rust_files,
            options.allow_partial,
            &mut file_reports,
        )?);
    }
    if !python_files.is_empty() {
        parsed.extend(python_parser::parse_python_functions(
            source_dir,
            &python_files,
            options.allow_partial,
            &mut file_reports,
        )?);
    }
    if !ts_files.is_empty() {
        parsed.extend(ts_parser::parse_typescript_functions(
            source_dir,
            &ts_files,
            options.allow_partial,
            &mut file_reports,
        )?);
    }

    let coverage = ExtractionCoverageReport::from_files(file_reports);
    if !options.allow_partial && !coverage.complete {
        return Err(LegitimacyError::invalid_input(format!(
            "extraction coverage incomplete for '{}': {} parsed, {} skipped, {} errored",
            source_dir.display(),
            coverage.files_parsed,
            coverage.files_skipped,
            coverage.files_errored
        )));
    }

    Ok(ParsedGovernanceSources {
        functions: parsed,
        coverage,
    })
}

fn collect_source_files(
    source_dir: &Path,
) -> Result<Vec<(PathBuf, SourceLanguage)>, LegitimacyError> {
    let metadata = fs::metadata(source_dir).map_err(|source| LegitimacyError::Io {
        context: format!("source directory '{}'", source_dir.display()),
        source,
    })?;
    if !metadata.is_dir() {
        return Err(LegitimacyError::invalid_input(format!(
            "extract source must be a directory, got '{}'",
            source_dir.display()
        )));
    }

    let mut files = Vec::new();
    let mut stack = vec![source_dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let mut entries = fs::read_dir(&dir)
            .map_err(|source| LegitimacyError::Io {
                context: format!("directory '{}'", dir.display()),
                source,
            })?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|source| LegitimacyError::Io {
                context: format!("directory '{}'", dir.display()),
                source,
            })?;
        entries.sort_by_key(|entry| entry.path());

        for entry in entries {
            let path = entry.path();
            let file_type = entry.file_type().map_err(|source| LegitimacyError::Io {
                context: format!("directory entry '{}'", path.display()),
                source,
            })?;
            if file_type.is_symlink() {
                continue;
            }
            if file_type.is_dir() {
                stack.push(path);
            } else if file_type.is_file()
                && !should_skip_source_file(&path)
                && let Some(language) = detect_language(&path)
            {
                files.push((path, language));
            }
        }
    }

    files.sort_by(|(left_path, left_language), (right_path, right_language)| {
        left_path
            .cmp(right_path)
            .then_with(|| left_language.cmp(right_language))
    });
    Ok(files)
}

fn detect_language(path: &Path) -> Option<SourceLanguage> {
    match path.extension().and_then(|extension| extension.to_str()) {
        Some("py") => Some(SourceLanguage::Python),
        Some("rs") => Some(SourceLanguage::Rust),
        Some("ts" | "tsx") => Some(SourceLanguage::TypeScript),
        _ => None,
    }
}

fn should_skip_source_file(path: &Path) -> bool {
    path.file_name()
        .and_then(|file_name| file_name.to_str())
        .is_some_and(|file_name| {
            let lower = file_name.to_ascii_lowercase();
            lower.contains(".test.")
                || lower.contains(".test-")
                || lower.contains(".spec.")
                || lower.contains(".spec-")
                || lower.ends_with(".d.ts")
        })
}

pub fn extract_governance_artifacts(
    source_dir: &Path,
    options: ExtractionOptions,
) -> Result<GovernanceExtractionArtifacts, LegitimacyError> {
    extract_governance_artifacts_with_review(source_dir, options, None)
}

pub fn extract_governance_artifacts_with_review(
    source_dir: &Path,
    options: ExtractionOptions,
    review_overlay: Option<&ExtractionReviewOverlay>,
) -> Result<GovernanceExtractionArtifacts, LegitimacyError> {
    if options.mode == ExtractionMode::TheoremBacked {
        if review_overlay.is_some() {
            return Err(LegitimacyError::invalid_input(
                "theorem-backed extraction does not accept heuristic review overlays",
            ));
        }
        let source_files = collect_source_files(source_dir)?;
        if source_files
            .iter()
            .all(|(_, language)| *language == SourceLanguage::Rust)
        {
            return rust_hook_core_graph::extract_rust_hook_core_artifacts(source_dir, options);
        }
        if source_files
            .iter()
            .all(|(_, language)| *language == SourceLanguage::Python)
        {
            return python_hook_core_graph::extract_python_hook_core_artifacts(source_dir, options);
        }
        if source_files
            .iter()
            .all(|(_, language)| *language == SourceLanguage::TypeScript)
        {
            return typescript_approval_core_graph::extract_typescript_approval_core_artifacts(
                source_dir, options,
            );
        }
        return Err(LegitimacyError::invalid_input(
            "theorem-backed extraction requires a single supported core language",
        ));
    }
    let parsed = parse_governance_sources(source_dir, options)?;
    let build = patterns::build_governance_graph_artifacts(&parsed.functions, review_overlay)?;
    let boundary_causal_safety = assess_boundary_causal_safety(&build.graph, &parsed.functions);
    Ok(GovernanceExtractionArtifacts {
        source_dir: source_dir.display().to_string(),
        graph: build.graph,
        coverage: parsed.coverage,
        recognized_nodes: build.recognized_nodes,
        recognized_edges: build.recognized_edges,
        resolution_issues: build.resolution_issues,
        review_overlay: review_overlay.map(|_| source_dir.display().to_string()),
        boundary_causal_safety,
    })
}
