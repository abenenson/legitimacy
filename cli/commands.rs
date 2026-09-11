use clap::{Args, Parser, Subcommand, ValueEnum};
use legitimacy::{Certificate, GovernanceDriftAlert, LedgerAuditReport, extract::ExtractionMode};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, path::PathBuf};

use crate::trajectory::CodexExecOutputTypeV0;
use crate::{audit_graph, input::ClaimCorpusInputProvenance, witness};

#[derive(Parser, Debug)]
#[command(
    name = "legitimacy",
    version,
    about = "Formal legitimacy checker for agentic AI governance"
)]
pub(crate) struct Cli {
    #[command(subcommand)]
    pub(crate) command: Option<Command>,
}

#[derive(Subcommand, Debug)]
pub(crate) enum Command {
    /// Parse and compile a .rule.toml policy file.
    Compile {
        /// Path to the policy file.
        policy: PathBuf,
        /// Permit full Young consistency above the exponential safety threshold.
        #[arg(long)]
        allow_exponential_consistency: bool,
    },
    /// Run paradox diagnostics against a .rule.toml policy.
    Paradox {
        /// Path to the policy file.
        policy: PathBuf,
        /// Permit full Young consistency above the exponential safety threshold.
        #[arg(long)]
        allow_exponential_consistency: bool,
    },
    /// Show factor-model exposure for a .rule.toml rule policy.
    Factor {
        /// Path to the policy file.
        policy: PathBuf,
        /// Permit full Young consistency above the exponential safety threshold.
        #[arg(long)]
        allow_exponential_consistency: bool,
    },
    /// Extract governance artifacts from source code.
    Extract {
        /// Root directory containing Rust source files.
        source_dir: PathBuf,
        /// Parse a Claude Code .claude/ directory instead of source code.
        #[arg(long)]
        claude_dir: bool,
        /// Allow partial extraction when some files fail to parse.
        #[arg(long)]
        allow_partial: bool,
        /// Extraction lane to use; heuristic is the backwards-compatible default.
        #[arg(long, value_enum, default_value = "heuristic")]
        mode: CliExtractionMode,
        /// Write the extracted governance graph JSON to this path.
        #[arg(long)]
        emit_graph: Option<PathBuf>,
        /// Write an AST-hash theorem witness JSON to this path.
        #[arg(long)]
        emit_theorem_witness: Option<PathBuf>,
        /// Lean theorem name bound into the emitted theorem witness.
        #[arg(long, default_value = "extracted_governance_graph_witness")]
        theorem_name: String,
        /// Optional review overlay JSON to promote curated nodes/edges and alias hints.
        #[arg(long)]
        review_overlay: Option<PathBuf>,
        /// Audit the extracted graph against a JSON/JSONL claim corpus.
        #[arg(long)]
        claims: Option<PathBuf>,
        /// Provenance label for the supplied claim corpus.
        #[arg(long, value_enum, default_value = "user-supplied")]
        claims_provenance: ClaimCorpusInputProvenance,
        /// Audit the extracted graph against the synthetic structural probe corpus.
        #[arg(long)]
        synthetic: bool,
    },
    /// Audit a governance graph against an explicit claim corpus.
    AuditGraph(audit_graph::AuditGraphCommand),
    /// Verify an AST-hash theorem witness against source and graph artifacts.
    VerifyWitness(witness::VerifyWitnessCommand),
    /// Declare sacrificed governance properties for a concrete rule policy.
    Sacrifice {
        /// Path to the policy file.
        policy: PathBuf,
        /// Permit full Young consistency above the exponential safety threshold.
        #[arg(long)]
        allow_exponential_consistency: bool,
    },
    /// Watch runtime governance observations and alert on sacrifice drift.
    Monitor {
        /// Path to the policy file.
        policy: PathBuf,
        /// Permit full Young consistency above the exponential safety threshold.
        #[arg(long)]
        allow_exponential_consistency: bool,
        /// Poll interval in seconds for the event source.
        #[arg(long, default_value_t = 60)]
        interval: u64,
    },
    /// Issue a certificate for a concrete claimant outcome.
    Certify {
        /// Path to the policy file.
        policy: PathBuf,
        /// Permit full Young consistency above the exponential safety threshold.
        #[arg(long)]
        allow_exponential_consistency: bool,
        /// Claimant ID to certify.
        #[arg(long)]
        claimant: String,
        /// Outcome allocated to the claimant.
        #[arg(long)]
        outcome: f64,
        /// Evidence entries of the form key=value.
        #[arg(long = "evidence", value_name = "KEY=VALUE")]
        evidence: Vec<String>,
    },
    /// Audit a historical stream of governed events.
    Audit {
        /// Optional path to the policy file when auditing an events stream.
        policy: Option<PathBuf>,
        /// Permit full Young consistency above the exponential safety threshold.
        #[arg(long)]
        allow_exponential_consistency: bool,
        /// Optional JSONL file containing audit events.
        #[arg(long)]
        events: Option<PathBuf>,
        /// Optional explicit ledger path. Defaults to the local legitimacy ledger.
        #[arg(long)]
        ledger: Option<PathBuf>,
        /// Filter historical results by rule name.
        #[arg(long = "rule-name")]
        rule_name: Option<String>,
        /// Filter historical results by rule version.
        #[arg(long = "rule-version")]
        rule_version: Option<String>,
        /// Filter historical results by claimant ID.
        #[arg(long)]
        claimant: Option<String>,
        /// Maximum rows to return from each ledger table.
        #[arg(long, default_value_t = 25)]
        limit: usize,
        /// Verify the tamper-evident chain across ledger tables.
        #[arg(long)]
        verify_chain: bool,
    },
    /// Operate the spectral governance protocol state machine.
    Protocol {
        #[command(subcommand)]
        command: ProtocolCommand,
    },
    /// Manage governance-corpus benchmark manifests.
    Corpus {
        #[command(subcommand)]
        command: CorpusCommand,
    },
    /// Adapt a sealed Codex 0.144.0 exec JSONL capture into a trajectory bundle.
    AdaptCodexExecV0 {
        /// Exact stdout JSONL attachment, including the final LF.
        #[arg(long)]
        raw_stdout_jsonl: PathBuf,
        /// Private typed authority receipt for the exact attachment.
        #[arg(long)]
        authority_receipt: PathBuf,
        /// Out-of-band expected commitment and downstream policy context.
        #[arg(long)]
        trusted_context: PathBuf,
        /// Explicit private or shareable-sanitized output type.
        #[arg(long, value_enum)]
        output_type: CodexExecOutputTypeV0,
        /// New output path; existing files are never replaced.
        #[arg(long)]
        output: PathBuf,
        /// Owner-private lineage sidecar required for shareable-sanitized output.
        #[arg(long, required_if_eq("output_type", "shareable-sanitized"))]
        private_lineage_output: Option<PathBuf>,
    },
    /// Materialize the official canonical bytes of a separately validated trajectory.
    CanonicalizeTrajectoryV0 {
        #[command(flatten)]
        inputs: TrajectoryValidationInputsV0,
        /// New output path; existing files are never replaced.
        #[arg(long)]
        output: PathBuf,
    },
    /// Build an unverified deterministic replay candidate from a validated trajectory.
    BuildTrajectoryReplayCandidateV0 {
        #[command(flatten)]
        inputs: TrajectoryValidationInputsV0,
        /// New output path; existing files are never replaced.
        #[arg(long)]
        output: PathBuf,
    },
    /// Independently recompute and sign a replay-authority receipt.
    IssueTrajectoryReplayAuthorityReceiptV0 {
        #[command(flatten)]
        inputs: TrajectoryValidationInputsV0,
        /// Owner-private file containing exactly 32 Ed25519 secret-key bytes.
        #[arg(long)]
        authority_private_key: PathBuf,
        /// Pinned lowercase authority issuer identity.
        #[arg(long)]
        issuer: String,
        /// Pinned lowercase authority key identity.
        #[arg(long)]
        key_id: String,
        /// Nonzero authority epoch accepted by the corresponding trust policy.
        #[arg(long)]
        authority_epoch: u64,
        /// New output path; existing files are never replaced.
        #[arg(long)]
        output: PathBuf,
    },
    /// Recompute replay integrity and verify a signed authority receipt.
    VerifyTrajectoryReplayV0 {
        #[command(flatten)]
        inputs: TrajectoryValidationInputsV0,
        /// Existing deterministic replay candidate JSON line.
        #[arg(long)]
        replay: PathBuf,
        /// Independently issued signed replay-authority receipt JSON line.
        #[arg(long)]
        authority_receipt: PathBuf,
        /// Separately configured pinned replay-authority trust policy JSON line.
        #[arg(long)]
        authority_trust_policy: PathBuf,
        /// New verified-success output path; existing files are never replaced.
        #[arg(long)]
        output: PathBuf,
    },
    /// Evaluate composition only from an adapter-derived Codex 0.144.0 trajectory.
    ///
    /// Re-adapts the exact stdout JSONL under the supplied input authority and trusted
    /// adaptation context, then verifies the independently authorized replay against that
    /// adapter-owned trace before evaluating the exact composition-policy bytes. This command
    /// accepts no caller-authored trace or normalized event values. It does not establish
    /// completeness, truth, intent access, enforcement, concurrency safety, principal
    /// discovery, or incident prevention.
    EvaluateCodexExecCompositionV0 {
        /// Exact Codex 0.144.0 stdout JSONL attachment, including the final LF.
        #[arg(long)]
        raw_stdout_jsonl: PathBuf,
        /// Existing private typed Codex input-authority receipt for the exact attachment.
        #[arg(
            long,
            requires = "trusted_adaptation_context",
            conflicts_with = "shareable_sanitized_bundle"
        )]
        input_authority_receipt: Option<PathBuf>,
        /// Existing trusted adaptation context binding private authority and policy.
        #[arg(
            long,
            requires = "input_authority_receipt",
            conflicts_with = "shareable_sanitized_bundle"
        )]
        trusted_adaptation_context: Option<PathBuf>,
        /// Closed public sanitized bundle used as typed derived authority and context.
        #[arg(
            long,
            required_unless_present = "input_authority_receipt",
            conflicts_with = "input_authority_receipt"
        )]
        shareable_sanitized_bundle: Option<PathBuf>,
        /// Optional owner-private sidecar for a separate exact parent-lineage admission.
        #[arg(long, requires = "shareable_sanitized_bundle")]
        private_lineage_sidecar: Option<PathBuf>,
        /// Inspected deterministic replay candidate to verify against the adapted trace.
        #[arg(long)]
        replay_candidate: PathBuf,
        /// Independently signed replay-authority receipt for the complete replay tuple.
        #[arg(long)]
        replay_authority_receipt: PathBuf,
        /// Separately configured pinned replay-authority trust policy.
        #[arg(long)]
        replay_authority_trust_policy: PathBuf,
        /// Exact canonical trajectory-composition policy bytes.
        #[arg(long)]
        composition_policy: PathBuf,
        /// Legacy result path; requires both legacy trace paths and is not crash-atomic.
        #[arg(long, requires_all = ["trace_output", "canonical_trace_output"], conflicts_with = "output_set")]
        output: Option<PathBuf>,
        /// Legacy official compact trace path; requires the complete legacy set.
        #[arg(long, requires_all = ["output", "canonical_trace_output"], conflicts_with = "output_set")]
        trace_output: Option<PathBuf>,
        /// Legacy exact canonical trace path; requires the complete legacy set.
        #[arg(long, requires_all = ["output", "trace_output"], conflicts_with = "output_set")]
        canonical_trace_output: Option<PathBuf>,
        /// New directory containing trace.json, canonical-trace.bin, and composition-result.json.
        #[arg(long, required_unless_present = "output")]
        output_set: Option<PathBuf>,
    },
}

#[derive(Args, Debug)]
pub(crate) struct TrajectoryValidationInputsV0 {
    /// Closed TrajectoryTraceV0 JSON wire.
    #[arg(long)]
    pub(crate) trace: PathBuf,
    /// Vendor-neutral JSON carrier containing exact ordered raw-record strings.
    #[arg(long)]
    pub(crate) raw_records: PathBuf,
    /// Declared adapter, policy, capture, and derivation bindings; no derivation is executed.
    #[arg(long)]
    pub(crate) declared_context: PathBuf,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
pub(crate) enum CliExtractionMode {
    Heuristic,
    TheoremBacked,
}

impl From<CliExtractionMode> for ExtractionMode {
    fn from(value: CliExtractionMode) -> Self {
        match value {
            CliExtractionMode::Heuristic => ExtractionMode::Heuristic,
            CliExtractionMode::TheoremBacked => ExtractionMode::TheoremBacked,
        }
    }
}

#[derive(Subcommand, Debug)]
pub(crate) enum ProtocolCommand {
    /// Declare and compile a governance graph policy.
    Init {
        /// Path to the graph policy file.
        policy: PathBuf,
    },
    /// Measure factor exposure for a compiled protocol state.
    Measure {
        /// Path to the serialized protocol state JSON file.
        state: PathBuf,
    },
    /// Activate monitoring for a measured protocol state.
    Activate {
        /// Path to the serialized protocol state JSON file.
        state: PathBuf,
        /// Minimum monitor interval in seconds.
        #[arg(long, default_value_t = 5)]
        min_interval_seconds: u64,
        /// Maximum monitor interval in seconds.
        #[arg(long, default_value_t = 10)]
        max_interval_seconds: u64,
        /// Deterministic seed used to randomize the monitor interval.
        #[arg(long, default_value_t = 0)]
        seed: u64,
    },
    /// Show a concise summary of the current protocol state.
    Status {
        /// Path to the serialized protocol state JSON file.
        state: PathBuf,
    },
    /// Audit the protocol ledger for certificate-chain and drift activity.
    Audit {
        /// Path to the serialized protocol state JSON file.
        state: PathBuf,
    },
}

#[derive(Subcommand, Debug)]
pub(crate) enum CorpusCommand {
    /// Create an empty governance-corpus manifest.
    Init {
        /// Corpus root directory.
        #[arg(long, default_value = "audits/corpus")]
        corpus_dir: PathBuf,
    },
    /// Add a pinned harness skeleton to the governance corpus.
    Add {
        /// Harness id.
        id: String,
        /// Upstream source repository URL.
        #[arg(long)]
        source_repo: Option<String>,
        /// Pinned upstream source commit.
        #[arg(long)]
        source_commit: Option<String>,
        /// License identifier or summary.
        #[arg(long)]
        license: Option<String>,
        /// Local extraction input path for this harness.
        #[arg(long)]
        extraction_input: Option<PathBuf>,
        /// Allow partial extractor results for this harness.
        #[arg(long)]
        allow_partial: bool,
        /// Corpus root directory.
        #[arg(long, default_value = "audits/corpus")]
        corpus_dir: PathBuf,
    },
    /// Run the extractor across all corpus harnesses with local inputs.
    Evaluate {
        /// Corpus root directory.
        #[arg(long, default_value = "audits/corpus")]
        corpus_dir: PathBuf,
    },
    /// Show manifest/report changes since the last committed evaluation.
    Diff {
        /// Corpus root directory.
        #[arg(long, default_value = "audits/corpus")]
        corpus_dir: PathBuf,
    },
}

#[derive(Debug, Deserialize)]
pub(crate) struct AuditEvent {
    #[serde(default)]
    pub(crate) event_id: Option<String>,
    #[serde(alias = "claimant")]
    pub(crate) claimant_id: String,
    pub(crate) outcome: f64,
    #[serde(default)]
    pub(crate) act_description: Option<String>,
    #[serde(default)]
    pub(crate) evidence: BTreeMap<String, String>,
}

#[derive(Debug, Serialize)]
pub(crate) struct ComplianceReport {
    pub(crate) policy_path: String,
    pub(crate) rule_name: String,
    pub(crate) rule_version: String,
    pub(crate) admissible: bool,
    pub(crate) events_total: usize,
    pub(crate) certified: usize,
    pub(crate) rejected: usize,
    pub(crate) compile_violations: Vec<String>,
    pub(crate) results: Vec<AuditResult>,
}

#[derive(Debug, Serialize)]
pub(crate) struct AuditResult {
    pub(crate) line: usize,
    pub(crate) event_id: Option<String>,
    pub(crate) claimant_id: String,
    pub(crate) outcome: f64,
    pub(crate) status: AuditStatus,
    pub(crate) reason: Option<String>,
    pub(crate) certificate: Option<Certificate>,
}

#[derive(Debug, Serialize)]
pub(crate) struct LedgerAuditOutput {
    pub(crate) audit: LedgerAuditReport,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) chain_verification: Option<legitimacy::ChainVerificationResult>,
}

#[derive(Debug, Serialize)]
pub(crate) struct ProtocolAuditOutput {
    pub(crate) state: String,
    pub(crate) certificates: usize,
    pub(crate) drift_alerts: usize,
    pub(crate) certificate_chain_valid: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) latest_drift: Option<GovernanceDriftAlert>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum AuditStatus {
    Certified,
    Rejected,
}
