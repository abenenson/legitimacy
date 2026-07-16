use clap::{Parser, ValueEnum};
use legitimacy::{
    ClaimCorpusProvenance, ExtractionOptions, GovernanceGraph, GovernanceNode, GovernanceProperty,
    LegitimacyError, MonitoringSpec, ProtocolDeclaredSacrifice, ProtocolError,
    audit_governance_graph, compile_protocol, declare,
    extract::{ExtractionMode, synthetic_claims},
    extract_governance_artifacts,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    fmt, fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

#[derive(Debug, Parser)]
#[command(
    name = "legitimacy-audit-agent",
    about = "Audit frontier-agent governance surfaces with theorem-backed evidence bundles",
    override_usage = "legitimacy-audit-agent --target <TARGET> [--mode extract] <SOURCE_PATH>\n       legitimacy-audit-agent --target <TARGET> --mode replay-committed"
)]
struct Cli {
    #[arg(long)]
    target: String,
    #[arg(long, value_enum, default_value_t = AuditMode::Extract)]
    mode: AuditMode,
    #[arg(help = "Source tree to extract; required unless --mode replay-committed")]
    source_path: Option<PathBuf>,
}

#[derive(Debug, Clone, Copy, ValueEnum, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum AuditMode {
    ReplayCommitted,
    Extract,
}

impl AuditMode {
    fn as_str(self) -> &'static str {
        match self {
            Self::ReplayCommitted => "replay-committed",
            Self::Extract => "extract",
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum Target {
    CodexCli,
    ClaudeAgentSdk,
    ClaudeCode,
}

impl Target {
    fn reason_code(self) -> &'static str {
        match self {
            Self::CodexCli => "codex_cli_monotonicity_rejected",
            Self::ClaudeAgentSdk => "claude_agent_sdk_monotonicity_rejected",
            Self::ClaudeCode => "claude_code_monotonicity_rejected",
        }
    }

    fn theorem(self) -> &'static str {
        match self {
            Self::CodexCli => "codexCliRejectionAndThresholdFacts",
            Self::ClaudeAgentSdk => "claudeAgentSdkRejectionAndThresholdFacts",
            Self::ClaudeCode => "claudeCodeCliRejectionAndThresholdFacts",
        }
    }

    fn monotonicity_theorem(self) -> &'static str {
        match self {
            Self::CodexCli => "codexHooksGovernanceAdmissibilityRejectsMonotonicity",
            Self::ClaudeAgentSdk => "claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity",
            Self::ClaudeCode => "claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity",
        }
    }

    fn c_star_theorem(self) -> &'static str {
        match self {
            Self::CodexCli => "codexHarnessDerived_C_star_value",
            Self::ClaudeAgentSdk => "claudeAgentSdkHarnessDerived_C_star_value",
            Self::ClaudeCode => "claudeCodeHarnessDerived_C_star_value",
        }
    }

    fn lean_module(self) -> &'static str {
        match self {
            Self::CodexCli => "Legitimacy.CaseStudies.CodexHarness",
            Self::ClaudeAgentSdk => "Legitimacy.CaseStudies.ClaudeAgentSdkHarness",
            Self::ClaudeCode => "Legitimacy.CaseStudies.ClaudeCodeHarness",
        }
    }

    fn lean_file_path(self) -> &'static str {
        match self {
            Self::CodexCli => "lean/Legitimacy/CaseStudies/CodexHarness.lean",
            Self::ClaudeAgentSdk => "lean/Legitimacy/CaseStudies/ClaudeAgentSdkHarness.lean",
            Self::ClaudeCode => "lean/Legitimacy/CaseStudies/ClaudeCodeHarness.lean",
        }
    }

    fn repaired_alternative(self) -> Option<&'static str> {
        match self {
            Self::CodexCli => Some("codexHarness_stage4_repaired_admissible"),
            Self::ClaudeAgentSdk | Self::ClaudeCode => None,
        }
    }

    fn graph_fixture(self) -> Option<&'static str> {
        match self {
            Self::CodexCli => Some("examples/graphs/codex-graph.json"),
            Self::ClaudeAgentSdk => Some("examples/graphs/claude-agent-sdk-graph.json"),
            Self::ClaudeCode => Some("examples/graphs/claude-code-graph.json"),
        }
    }

    fn graph_fixture_commit(self) -> Option<&'static str> {
        match self {
            Self::CodexCli => Some(env!("LEGITIMACY_CODEX_GRAPH_COMMIT")),
            Self::ClaudeAgentSdk => Some(env!("LEGITIMACY_CLAUDE_AGENT_SDK_GRAPH_COMMIT")),
            Self::ClaudeCode => Some(env!("LEGITIMACY_CLAUDE_CODE_GRAPH_COMMIT")),
        }
    }

    fn extraction_mode(self) -> ExtractionMode {
        match self {
            Self::CodexCli | Self::ClaudeAgentSdk | Self::ClaudeCode => {
                ExtractionMode::TheoremBacked
            }
        }
    }

    fn c_star_value(self) -> Option<&'static str> {
        match self {
            Self::CodexCli | Self::ClaudeAgentSdk | Self::ClaudeCode => Some("1/10"),
        }
    }

    fn c_star_carrier_graph(self) -> &'static str {
        match self {
            Self::CodexCli => {
                "codexHarnessDerivedSpectralGraph: GovGraph ℚ 16 (derived from extracted graph; disconnected, 8 components)"
            }
            Self::ClaudeAgentSdk => {
                "claudeAgentSdkHarnessDerivedSpectralGraph: GovGraph ℚ 22 (derived from extracted graph; disconnected, 8 K₂ pairs + 6 isolated nodes)"
            }
            Self::ClaudeCode => {
                "claudeCodeHarnessDerivedSpectralGraph: GovGraph ℚ 31 (derived from extracted graph; disconnected, 14 K₂ pairs + 3 isolated nodes)"
            }
        }
    }

    fn named_feature(self) -> &'static str {
        match self {
            Self::CodexCli => "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse",
            Self::ClaudeAgentSdk => {
                "claude_agent_sdk/hooks.py::registration::PreToolUse::pre_tool_use_permission_decision"
            }
            Self::ClaudeCode => {
                "claude_code/public_governance_surface.py::registration::PreToolUse::pre_tool_use_permission_decision"
            }
        }
    }

    fn c_star_disclaimer(self) -> &'static str {
        match self {
            Self::CodexCli => {
                "the C* carrier graph is derived from the committed extracted graph by symmetrizing the pass-through topology; it is disconnected with 8 components"
            }
            Self::ClaudeAgentSdk => {
                "the C* carrier graph is derived from the committed extracted graph by symmetrizing the pass-through topology; it is disconnected with 8 K₂ components and 6 isolated nodes"
            }
            Self::ClaudeCode => {
                "the C* carrier graph is derived from the committed extracted graph by symmetrizing the pass-through topology; it is disconnected with 14 K₂ components and 3 isolated nodes"
            }
        }
    }
}

impl TryFrom<&str> for Target {
    type Error = AuditRefusal;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "codex-cli" => Ok(Self::CodexCli),
            "claude-agent-sdk" => Ok(Self::ClaudeAgentSdk),
            "claude-code" => Ok(Self::ClaudeCode),
            other => Err(AuditRefusal {
                reason_code: "unknown_target",
                message: format!("unsupported audit target '{other}'"),
            }),
        }
    }
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum Verdict {
    Admissible,
    Rejected { reason: RejectionReason },
    RequiresSacrifice { property: GovernanceProperty },
}

#[derive(Debug, Serialize)]
struct RejectionReason {
    code: String,
    diagnostic: String,
    named_feature: String,
}

#[derive(Debug, Serialize)]
struct SourcePointer {
    file: String,
    line_start: usize,
    line_end: usize,
    named_feature: String,
}

#[derive(Debug, Serialize)]
struct LeanEvidence {
    theorem_class: Option<String>,
    monotonicity_theorem: Option<String>,
    c_star_theorem: Option<String>,
    graph_cardinality_with_c_star_carrier_theorem: Option<String>,
    module: String,
    file_path: String,
    native_decide_fixture: bool,
    theorem_applicability: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    divergence: Option<LeanDivergence>,
}

#[derive(Debug, Clone, Serialize)]
struct LeanDivergence {
    expected_sha256: String,
    actual_sha256: String,
    expected_nodes: usize,
    actual_nodes: usize,
}

#[derive(Debug, Serialize)]
struct CapabilityThreshold {
    c_star: Option<String>,
    delta: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    computed_from: Option<String>,
    c_star_value_proved_on: String,
    extracted_graph_context: String,
    c_star_disclaimer: String,
}

#[derive(Debug, Serialize)]
struct ActivationGateEvidence {
    state: String,
    refusal: String,
    required_certificate_format: ProtocolDeclaredSacrifice,
}

#[derive(Debug, Serialize)]
struct EvidenceProvenance {
    mode: AuditMode,
    source_path: String,
    binary_version: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    extracted_graph_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    committed_graph_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    committed_graph_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    committed_graph_commit: Option<String>,
    statement: String,
}

#[derive(Debug, Serialize)]
struct EvidenceBundle {
    target: Target,
    verdict: Verdict,
    activation_verdict: Verdict,
    #[serde(skip_serializing_if = "Option::is_none")]
    extracted_governance_graph: Option<GovernanceGraph>,
    #[serde(skip_serializing_if = "Option::is_none")]
    replayed_governance_graph: Option<GovernanceGraph>,
    provenance: EvidenceProvenance,
    source_pointer: SourcePointer,
    lean: LeanEvidence,
    capability_threshold: CapabilityThreshold,
    activation_gate: ActivationGateEvidence,
    repaired_alternative: Option<String>,
}

#[derive(Debug, Serialize)]
struct RefusalBundle {
    verdict: Verdict,
    reason_code: &'static str,
    message: String,
}

#[derive(Debug)]
struct AuditRefusal {
    reason_code: &'static str,
    message: String,
}

struct GraphInput {
    graph: GovernanceGraph,
    source_pointer: SourcePointer,
    provenance: EvidenceProvenance,
    named_feature: String,
    fixture_backed: bool,
    theorem_applicability: TheoremApplicability,
}

struct LoadedGraphFixture {
    graph: GovernanceGraph,
    relative_path: &'static str,
    sha256: String,
    canonical_sha256: String,
    node_count: usize,
}

#[derive(Debug, Clone, Copy)]
struct GraphStructuralFacts {
    node_count: usize,
    edge_count: usize,
    gate_count: usize,
}

#[derive(Debug, Clone)]
enum TheoremApplicability {
    MatchesCommittedFixture,
    ExtractedDiagnosticOnly(LeanDivergence),
}

impl TheoremApplicability {
    fn as_str(&self) -> &'static str {
        match self {
            Self::MatchesCommittedFixture => "matches_committed_fixture",
            Self::ExtractedDiagnosticOnly(_) => "extracted_diagnostic_only",
        }
    }

    fn divergence(&self) -> Option<LeanDivergence> {
        match self {
            Self::MatchesCommittedFixture => None,
            Self::ExtractedDiagnosticOnly(divergence) => Some(divergence.clone()),
        }
    }
}

impl GraphStructuralFacts {
    fn from_graph(graph: &GovernanceGraph) -> Self {
        Self {
            node_count: graph.nodes.len(),
            edge_count: graph.edges.len(),
            gate_count: graph.nodes.values().map(node_gate_count).sum(),
        }
    }
}

impl fmt::Display for AuditRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.reason_code, self.message)
    }
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match run(cli) {
        Ok(bundle) => emit_json(&bundle).map_or(ExitCode::FAILURE, |_| {
            if matches!(bundle.verdict, Verdict::Rejected { .. }) {
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            }
        }),
        Err(refusal) => {
            let bundle = RefusalBundle {
                verdict: Verdict::Rejected {
                    reason: RejectionReason {
                        code: refusal.reason_code.to_string(),
                        diagnostic: "audit refusal".to_string(),
                        named_feature: "target_or_source".to_string(),
                    },
                },
                reason_code: refusal.reason_code,
                message: refusal.message,
            };
            let _ = emit_json(&bundle);
            ExitCode::FAILURE
        }
    }
}

fn run(cli: Cli) -> Result<EvidenceBundle, AuditRefusal> {
    let target = Target::try_from(cli.target.as_str())?;
    let mode = target.extraction_mode();

    let input = match cli.mode {
        AuditMode::ReplayCommitted => {
            if cli.source_path.is_some() {
                return Err(AuditRefusal {
                    reason_code: "source_path_for_replay_mode",
                    message: "--mode replay-committed and <SOURCE_PATH> are mutually exclusive"
                        .to_string(),
                });
            }
            replay_committed_input(target)?
        }
        AuditMode::Extract => extract_input(target, mode, cli.source_path.as_deref())?,
    };
    let named_feature = input.named_feature.clone();
    let graph = input.graph;
    let claims = synthetic_claims(&graph);
    let audit_result = audit_governance_graph(
        &graph,
        claims,
        ClaimCorpusProvenance::Fixture,
        Default::default(),
    );

    let (verdict, property) = match audit_result {
        Ok(audit) => {
            let rejected = audit.axiom_results.iter().find_map(|result| {
                matches!(result.verdict, Some(legitimacy::Verdict::Rejected { .. }))
                    .then(|| result.axiom.clone())
            });
            let property = rejected
                .as_deref()
                .and_then(property_from_axiom)
                .unwrap_or(GovernanceProperty::Monotonicity);
            let verdict = match rejected {
                Some(diagnostic) => Verdict::Rejected {
                    reason: RejectionReason {
                        code: target.reason_code().to_string(),
                        diagnostic,
                        named_feature: named_feature.clone(),
                    },
                },
                None => Verdict::Admissible,
            };
            (verdict, property)
        }
        Err(error) if !input.fixture_backed => (
            Verdict::Rejected {
                reason: RejectionReason {
                    code: "audit_evaluation_failed".to_string(),
                    diagnostic: error.to_string(),
                    named_feature: named_feature.clone(),
                },
            },
            GovernanceProperty::Monotonicity,
        ),
        Err(error) => {
            return Err(AuditRefusal {
                reason_code: "audit_evaluation_failed",
                message: error.to_string(),
            });
        }
    };

    let required_certificate_format = required_sacrifice(property, target);
    let activation_refusal = activation_refusal(&graph);
    let graph_facts = GraphStructuralFacts::from_graph(&graph);
    let provenance_mode = input.provenance.mode;
    let (extracted_governance_graph, replayed_governance_graph) = match provenance_mode {
        AuditMode::Extract => (Some(graph), None),
        AuditMode::ReplayCommitted => (None, Some(graph)),
    };

    Ok(EvidenceBundle {
        target,
        verdict,
        activation_verdict: Verdict::RequiresSacrifice { property },
        extracted_governance_graph,
        replayed_governance_graph,
        provenance: input.provenance,
        source_pointer: input.source_pointer,
        lean: lean_evidence(target, &input.theorem_applicability),
        capability_threshold: capability_threshold(
            target,
            provenance_mode,
            graph_facts,
            &input.theorem_applicability,
        ),
        activation_gate: ActivationGateEvidence {
            state: "requires_declared_sacrifice".to_string(),
            refusal: activation_refusal,
            required_certificate_format,
        },
        repaired_alternative: target.repaired_alternative().map(str::to_string),
    })
}

fn replay_committed_input(target: Target) -> Result<GraphInput, AuditRefusal> {
    let fixture = load_committed_graph(target)?;
    Ok(GraphInput {
        graph: fixture.graph,
        source_pointer: replay_source_pointer(target, fixture.relative_path),
        provenance: EvidenceProvenance {
            mode: AuditMode::ReplayCommitted,
            source_path: committed_graph_source_path(fixture.relative_path)?,
            binary_version: binary_version(),
            extracted_graph_sha256: None,
            committed_graph_sha256: Some(fixture.sha256),
            committed_graph_path: Some(fixture.relative_path.to_string()),
            committed_graph_commit: target.graph_fixture_commit().map(str::to_string),
            statement: format!(
                "This bundle replays the committed {} audit fixture. The \
                 committed_graph_sha256 field hashes the raw checked-in graph fixture bytes; \
                 replayed_governance_graph below is loaded from that fixture and is NOT the \
                 result of running extraction on --source-path.",
                target_label(target)
            ),
        },
        named_feature: target.named_feature().to_string(),
        fixture_backed: true,
        theorem_applicability: TheoremApplicability::MatchesCommittedFixture,
    })
}

fn extract_input(
    target: Target,
    mode: ExtractionMode,
    source_path: Option<&Path>,
) -> Result<GraphInput, AuditRefusal> {
    let Some(source_path) = source_path else {
        return Err(AuditRefusal {
            reason_code: "missing_source_path",
            message: "source path argument is required in --mode extract".to_string(),
        });
    };
    if !source_path.is_dir() {
        return Err(AuditRefusal {
            reason_code: "missing_source_path",
            message: format!("source path '{}' is not a directory", source_path.display()),
        });
    }

    let extracted = extract_governance_artifacts(
        source_path,
        ExtractionOptions {
            allow_partial: false,
            mode,
        },
    )
    .map_err(|error| AuditRefusal {
        reason_code: "malformed_graph_extraction",
        message: error.to_string(),
    })?;
    let graph = extracted.graph.clone();
    let extracted_graph_sha256 = graph_sha256(&graph)?;
    let fixture = load_committed_graph(target)?;
    let theorem_applicability =
        theorem_applicability_for_extraction(&graph, &extracted_graph_sha256, &fixture);
    let source_pointer = source_pointer(&extracted, target);
    let named_feature = target.named_feature().to_string();
    let resolved_source_path = resolved_source_path(source_path)?;

    Ok(GraphInput {
        graph,
        source_pointer,
        provenance: EvidenceProvenance {
            mode: AuditMode::Extract,
            source_path: resolved_source_path,
            binary_version: binary_version(),
            extracted_graph_sha256: Some(extracted_graph_sha256),
            committed_graph_sha256: None,
            committed_graph_path: None,
            committed_graph_commit: None,
            statement: "This bundle was produced by running formal-subset extraction on \
                        --source-path recorded in provenance.source_path; \
                        extracted_graph_sha256 hashes the normalized in-memory extracted graph."
                .to_string(),
        },
        named_feature,
        fixture_backed: false,
        theorem_applicability,
    })
}

fn load_committed_graph(target: Target) -> Result<LoadedGraphFixture, AuditRefusal> {
    let Some(relative_path) = target.graph_fixture() else {
        return Err(AuditRefusal {
            reason_code: target.reason_code(),
            message: "target has no committed graph fixture".to_string(),
        });
    };
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative_path);
    let bytes = fs::read(&path).map_err(|error| AuditRefusal {
        reason_code: "graph_fixture_unreadable",
        message: format!("failed to read '{}': {error}", path.display()),
    })?;
    let graph = serde_json::from_slice(&bytes).map_err(|error| AuditRefusal {
        reason_code: "graph_fixture_malformed",
        message: format!("failed to parse '{}': {error}", path.display()),
    })?;
    let canonical_sha256 = graph_sha256(&graph)?;
    let node_count = graph.nodes.len();
    Ok(LoadedGraphFixture {
        graph,
        relative_path,
        sha256: sha256_label(&bytes),
        canonical_sha256,
        node_count,
    })
}

fn source_pointer(
    extracted: &legitimacy::GovernanceExtractionArtifacts,
    target: Target,
) -> SourcePointer {
    let preferred = match target {
        Target::CodexCli => "on_UserPromptSubmit",
        Target::ClaudeAgentSdk => "pre_tool_use_permission_decision",
        Target::ClaudeCode => "pre_tool_use_permission_decision",
    };
    let node = extracted
        .recognized_nodes
        .iter()
        .find(|node| node.function_name == preferred)
        .or_else(|| extracted.recognized_nodes.first());
    SourcePointer {
        file: node
            .map(|node| node.relative_path.clone())
            .unwrap_or_else(|| extracted.source_dir.clone()),
        line_start: node.map_or(0, |node| node.line_start),
        line_end: node.map_or(0, |node| node.line_end),
        named_feature: node
            .map(|node| node.node_id.clone())
            .unwrap_or_else(|| target.named_feature().to_string()),
    }
}

fn replay_source_pointer(target: Target, fallback_path: &str) -> SourcePointer {
    SourcePointer {
        file: fallback_path.to_string(),
        line_start: 0,
        line_end: 0,
        named_feature: target.named_feature().to_string(),
    }
}

fn lean_evidence(target: Target, applicability: &TheoremApplicability) -> LeanEvidence {
    let theorem_applicability = applicability.as_str().to_string();
    let divergence = applicability.divergence();
    let theorem_fields_apply =
        matches!(applicability, TheoremApplicability::MatchesCommittedFixture);
    LeanEvidence {
        theorem_class: theorem_fields_apply.then(|| target.theorem().to_string()),
        monotonicity_theorem: theorem_fields_apply
            .then(|| target.monotonicity_theorem().to_string()),
        c_star_theorem: theorem_fields_apply.then(|| target.c_star_theorem().to_string()),
        graph_cardinality_with_c_star_carrier_theorem: theorem_fields_apply.then(|| {
            match target {
                Target::CodexCli => "codexExtractedGraphCardinalityAndCStar",
                Target::ClaudeAgentSdk => "claudeAgentSdkExtractedGraphCardinalityAndCStar",
                Target::ClaudeCode => "claudeCodeExtractedGraphCardinalityAndCStar",
            }
            .to_string()
        }),
        module: target.lean_module().to_string(),
        file_path: target.lean_file_path().to_string(),
        native_decide_fixture: theorem_fields_apply,
        theorem_applicability,
        divergence,
    }
}

fn capability_threshold(
    target: Target,
    mode: AuditMode,
    graph_facts: GraphStructuralFacts,
    applicability: &TheoremApplicability,
) -> CapabilityThreshold {
    let theorem_fields_apply =
        matches!(applicability, TheoremApplicability::MatchesCommittedFixture);
    CapabilityThreshold {
        c_star: theorem_fields_apply
            .then(|| target.c_star_value().unwrap_or("unavailable").to_string()),
        delta: theorem_fields_apply.then(|| "1/10".to_string()),
        computed_from: (!theorem_fields_apply).then(|| {
            "extracted graph diverged from committed fixture; no finite Lean fixture theorem applies"
                .to_string()
        }),
        c_star_value_proved_on: if theorem_fields_apply {
            format!(
                "{} on {}",
                target.c_star_theorem(),
                target.c_star_carrier_graph()
            )
        } else {
            "unavailable_for_divergent_extraction".to_string()
        },
        extracted_graph_context: format!(
            "mode={}; extracted_node_count={}; edges={}; gates={}",
            mode.as_str(),
            graph_facts.node_count,
            graph_facts.edge_count,
            graph_facts.gate_count
        ),
        c_star_disclaimer: target.c_star_disclaimer().to_string(),
    }
}

fn theorem_applicability_for_extraction(
    graph: &GovernanceGraph,
    extracted_graph_sha256: &str,
    fixture: &LoadedGraphFixture,
) -> TheoremApplicability {
    if extracted_graph_sha256 == fixture.canonical_sha256 {
        TheoremApplicability::MatchesCommittedFixture
    } else {
        TheoremApplicability::ExtractedDiagnosticOnly(LeanDivergence {
            expected_sha256: fixture.canonical_sha256.clone(),
            actual_sha256: extracted_graph_sha256.to_string(),
            expected_nodes: fixture.node_count,
            actual_nodes: graph.nodes.len(),
        })
    }
}

fn node_gate_count(node: &GovernanceNode) -> usize {
    match node {
        GovernanceNode::Binary { gates, .. } => gates.len(),
        GovernanceNode::Proportional { .. } | GovernanceNode::Threshold { .. } => 0,
    }
}

fn graph_sha256(graph: &GovernanceGraph) -> Result<String, AuditRefusal> {
    let bytes = serde_json::to_vec(graph).map_err(|error| AuditRefusal {
        reason_code: "graph_hash_failed",
        message: error.to_string(),
    })?;
    Ok(sha256_label(&bytes))
}

fn sha256_label(bytes: &[u8]) -> String {
    format!("sha256:{:x}", Sha256::digest(bytes))
}

fn binary_version() -> String {
    format!(
        "legitimacy-audit-agent {} ({})",
        env!("CARGO_PKG_VERSION"),
        env!("LEGITIMACY_BUILD_GIT_COMMIT")
    )
}

fn resolved_source_path(source_path: &Path) -> Result<String, AuditRefusal> {
    source_path
        .canonicalize()
        .map(|path| path.display().to_string())
        .map_err(|error| AuditRefusal {
            reason_code: "source_path_unresolved",
            message: format!(
                "failed to resolve source path '{}': {error}",
                source_path.display()
            ),
        })
}

fn committed_graph_source_path(relative_path: &str) -> Result<String, AuditRefusal> {
    resolved_source_path(&Path::new(env!("CARGO_MANIFEST_DIR")).join(relative_path))
}

fn target_label(target: Target) -> &'static str {
    match target {
        Target::CodexCli => "Codex CLI",
        Target::ClaudeAgentSdk => "Claude Agent SDK",
        Target::ClaudeCode => "Claude Code",
    }
}

fn activation_refusal(graph: &GovernanceGraph) -> String {
    let declared = match declare(graph.clone(), Vec::new()) {
        Ok(declared) => declared,
        Err(error) => return activation_refusal_message(error),
    };
    match compile_protocol(declared) {
        Ok(_) => "compiled_without_required_sacrifice".to_string(),
        Err(error) => activation_refusal_message(error),
    }
}

fn activation_refusal_message(error: ProtocolError) -> String {
    format!(
        "activation refused before live promotion: {error}; submit a DeclaredSacrifice \
         certificate for the reported diagnostic before retrying"
    )
}

fn required_sacrifice(property: GovernanceProperty, target: Target) -> ProtocolDeclaredSacrifice {
    ProtocolDeclaredSacrifice {
        property,
        justification: format!(
            "Declare and monitor the forced {} sacrifice for {}.",
            property.as_str(),
            target.reason_code()
        ),
        monitoring_specs: vec![MonitoringSpec {
            metric: property.as_str().to_string(),
            threshold: 1.0,
            frequency_seconds: 300,
            alert_channel: "governance-risk".to_string(),
        }],
    }
}

fn property_from_axiom(value: &str) -> Option<GovernanceProperty> {
    match value {
        "graph consistency" => Some(GovernanceProperty::Consistency),
        "graph solidarity" => Some(GovernanceProperty::Solidarity),
        "graph monotonicity" => Some(GovernanceProperty::Monotonicity),
        "graph strategyproofness" => Some(GovernanceProperty::Strategyproofness),
        "graph certifiability" => Some(GovernanceProperty::Certifiability),
        "graph observable determinacy" => Some(GovernanceProperty::ObservableDeterminacy),
        "graph corrigibility" => Some(GovernanceProperty::Corrigibility),
        "graph compositional safety" => Some(GovernanceProperty::CompositionalSafety),
        "graph nonvacuity" => Some(GovernanceProperty::NonVacuous),
        _ => None,
    }
}

fn emit_json<T: Serialize>(value: &T) -> Result<(), LegitimacyError> {
    println!(
        "{}",
        serde_json::to_string_pretty(value).map_err(|source| {
            LegitimacyError::Serialize {
                context: "audit-agent evidence bundle".to_string(),
                source,
            }
        })?
    );
    Ok(())
}
