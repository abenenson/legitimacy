use legitimacy::{ExtractionOptions, extract::ExtractionMode, extract_governance_artifacts};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn theorem_options() -> ExtractionOptions {
    ExtractionOptions {
        allow_partial: false,
        mode: ExtractionMode::TheoremBacked,
    }
}

fn extracted_graph_value(source_path: &str) -> Value {
    let artifacts = extract_governance_artifacts(Path::new(source_path), theorem_options())
        .expect("fixture should extract independently");
    serde_json::to_value(artifacts.graph).unwrap()
}

fn committed_fixture_hash(path: &str) -> String {
    let bytes = fs::read(path).unwrap();
    format!("sha256:{:x}", Sha256::digest(bytes))
}

fn committed_fixture_commit(path: &str) -> String {
    let output = Command::new("git")
        .args(["log", "-n", "1", "--format=%H", "--", path])
        .output()
        .unwrap();
    assert!(output.status.success(), "git log failed: {output:?}");
    String::from_utf8(output.stdout).unwrap().trim().to_string()
}

fn extracted_graph_hash(source_path: &str) -> String {
    let artifacts = extract_governance_artifacts(Path::new(source_path), theorem_options())
        .expect("fixture should extract independently");
    let bytes = serde_json::to_vec(&artifacts.graph).unwrap();
    format!("sha256:{:x}", Sha256::digest(bytes))
}

fn committed_graph_value(path: &str) -> Value {
    serde_json::from_slice(&fs::read(path).unwrap()).unwrap()
}

fn assert_graph_cardinality_with_c_star_field(bundle: &Value, theorem: &str) {
    assert!(
        bundle["lean"]
            .get("spectral_correspondence_theorem")
            .is_none(),
        "lean.spectral_correspondence_theorem should not be emitted"
    );
    assert_eq!(
        bundle["lean"]["graph_cardinality_with_c_star_carrier_theorem"],
        theorem
    );
}

fn assert_capability_threshold_labels_carrier_and_extracted_context(
    bundle: &Value,
    carrier_graph: &str,
    disclaimer_substring: &str,
) {
    let threshold = &bundle["capability_threshold"];
    assert_eq!(threshold["c_star_value_proved_on"], carrier_graph);
    assert!(
        threshold.get("computed_from").is_none(),
        "capability_threshold.computed_from should be split into explicit carrier and extracted graph context fields"
    );
    let extracted_graph_context = threshold["extracted_graph_context"].as_str().unwrap();
    assert!(
        extracted_graph_context.contains("extracted_node_count="),
        "capability_threshold.extracted_graph_context should identify extracted graph cardinality"
    );
    assert!(
        !extracted_graph_context.contains("spectral_cardinality="),
        "capability_threshold.extracted_graph_context should not label extracted nodes as spectral cardinality"
    );
    assert!(
        threshold["c_star_disclaimer"]
            .as_str()
            .unwrap()
            .contains(disclaimer_substring),
        "capability_threshold.c_star_disclaimer should state the expected carrier provenance"
    );
}

fn assert_binary_version_matches_package(bundle: &Value) {
    let binary_version = bundle["provenance"]["binary_version"]
        .as_str()
        .expect("provenance.binary_version should be emitted");
    assert!(
        binary_version.contains(env!("CARGO_PKG_VERSION")),
        "binary_version should include CARGO_PKG_VERSION: {binary_version}"
    );
}

fn audit_agent_bundle(target: &str, source_path: &str) -> Value {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", target, source_path])
        .output()
        .unwrap();
    assert!(
        !output.status.success(),
        "rejected audit-agent verdict should exit non-zero: {output:?}"
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn copy_dir_all(source: &Path, destination: &Path) {
    fs::create_dir_all(destination).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let file_type = entry.file_type().unwrap();
        let destination_path = destination.join(entry.file_name());
        if file_type.is_dir() {
            copy_dir_all(&entry.path(), &destination_path);
        } else {
            fs::copy(entry.path(), destination_path).unwrap();
        }
    }
}

fn temp_fixture_copy(source_path: &str, name: &str) -> PathBuf {
    let destination = std::env::temp_dir().join(format!(
        "legitimacy-audit-agent-{name}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&destination);
    copy_dir_all(Path::new(source_path), &destination);
    destination
}

fn assert_fixture_extracts_to_committed_graph(source_path: &str, graph_path: &str) {
    assert_eq!(
        extracted_graph_value(source_path),
        committed_graph_value(graph_path)
    );
}

fn assert_theorem_file_text_matches_graph(
    lean_path: &str,
    theorem_lean_path: &str,
    graph_constant: &str,
    graph_bound_theorems: &[&str],
    graph: &Value,
) {
    let lean = fs::read_to_string(lean_path).unwrap();
    let theorem_lean = if theorem_lean_path == lean_path {
        lean.clone()
    } else {
        fs::read_to_string(theorem_lean_path).unwrap()
    };
    for theorem in graph_bound_theorems {
        assert_theorem_statement_mentions_graph(
            theorem_lean_path,
            &theorem_lean,
            theorem,
            graph_constant,
        );
    }

    let nodes = graph["nodes"].as_object().unwrap();
    for (node_id, node) in nodes {
        let binary = node["Binary"].as_object().unwrap();
        assert!(
            lean.contains(&format!(".binary {node_id:?}")),
            "Lean fixture {lean_path} is missing binary node {node_id}"
        );
        let name = binary["name"].as_str().unwrap();
        assert!(
            lean.contains(&format!("{name:?}")),
            "Lean fixture {lean_path} is missing node name {name}"
        );
        for gate in binary["gates"].as_array().unwrap() {
            assert_lean_contains_gate(lean_path, &lean, gate);
        }
    }

    for edge in graph["edges"].as_array().unwrap() {
        let from = edge["from"].as_str().unwrap();
        let to = edge["to"].as_str().unwrap();
        let snippet =
            format!("{{ fromNode := {from:?}, toNode := {to:?}, transform := .passThrough }}");
        assert!(
            lean.contains(&snippet),
            "Lean fixture {lean_path} is missing edge {from} -> {to}"
        );
    }
}

fn assert_theorem_statement_mentions_graph(
    lean_path: &str,
    lean: &str,
    theorem: &str,
    graph_constant: &str,
) {
    let statement = theorem_statement(lean, theorem)
        .unwrap_or_else(|| panic!("Lean fixture {lean_path} is missing theorem {theorem}"));
    assert!(
        statement.contains(graph_constant),
        "theorem {theorem} in {lean_path} does not mention graph constant {graph_constant}"
    );
}

fn theorem_statement<'a>(lean: &'a str, theorem: &str) -> Option<&'a str> {
    let declaration = format!("theorem {theorem}");
    let start = lean.find(&declaration)?;
    let rest = &lean[start..];
    let end = rest.find(":= by")?;
    Some(&rest[..end])
}

fn assert_lean_contains_gate(lean_path: &str, lean: &str, gate: &Value) {
    let gate = gate.as_object().unwrap();
    let (kind, payload) = gate.iter().next().unwrap();
    let snippet = match kind.as_str() {
        "ExactMatch" => {
            let value = payload["value"].as_str().unwrap();
            let decision = lean_decision(payload["decision"].as_str().unwrap());
            format!(".exactMatch {value:?} {decision}")
        }
        "ThresholdGate" => {
            let field = payload["field"].as_str().unwrap();
            let min = payload["min"].as_f64().unwrap();
            let min = if min.fract() == 0.0 {
                format!("{}", min as i64)
            } else {
                min.to_string()
            };
            let decision = lean_decision(payload["decision"].as_str().unwrap());
            format!(".thresholdGate {field:?} {min} {decision}")
        }
        other => panic!("binding test does not yet render {other} gates"),
    };
    assert!(
        lean.contains(&snippet),
        "Lean fixture {lean_path} is missing gate {snippet}"
    );
}

fn lean_decision(decision: &str) -> &'static str {
    match decision {
        "Permit" => ".permit",
        "Deny" => ".deny",
        "Escalate" => ".escalate",
        other => panic!("unknown graph decision {other}"),
    }
}

fn assert_audit_agent_graph_text_matches_lean_fixture_constant(
    target: &str,
    source_path: &str,
    graph_path: &str,
    lean_path: &str,
    graph_constant: &str,
    graph_bound_theorems: &[&str],
) {
    let bundle = audit_agent_bundle(target, source_path);
    let emitted = bundle["extracted_governance_graph"].clone();
    let committed = committed_graph_value(graph_path);
    assert_eq!(
        emitted, committed,
        "audit-agent extract-mode graph for {target} drifted from committed fixture"
    );
    let theorem_lean_path = bundle["lean"]["file_path"]
        .as_str()
        .expect("audit-agent bundle should include lean.file_path");
    assert_theorem_file_text_matches_graph(
        lean_path,
        theorem_lean_path,
        graph_constant,
        graph_bound_theorems,
        &committed,
    );
}

fn assert_committed_fixture_theorems_apply(bundle: &Value) {
    assert_eq!(
        bundle["lean"]["theorem_applicability"],
        "matches_committed_fixture"
    );
    assert!(
        bundle["lean"].get("divergence").is_none(),
        "canonical fixture bundles should not emit lean.divergence"
    );
}

fn assert_divergent_extraction_is_diagnostic_only(
    target: &str,
    source_path: &Path,
    committed_source_path: &str,
    committed_graph_path: &str,
) {
    let bundle = audit_agent_bundle(target, source_path.to_str().unwrap());
    let actual_hash = extracted_graph_hash(source_path.to_str().unwrap());
    let expected_hash = extracted_graph_hash(committed_source_path);
    let actual_nodes = bundle["extracted_governance_graph"]["nodes"]
        .as_object()
        .unwrap()
        .len();
    let expected_nodes = committed_graph_value(committed_graph_path)["nodes"]
        .as_object()
        .unwrap()
        .len();

    assert_eq!(
        bundle["lean"]["theorem_applicability"],
        "extracted_diagnostic_only"
    );
    assert!(
        bundle["lean"]["theorem_class"].is_null(),
        "divergent extraction must not cite theorem_class"
    );
    assert!(
        bundle["lean"]["monotonicity_theorem"].is_null(),
        "divergent extraction must not cite monotonicity theorem"
    );
    assert!(
        bundle["lean"]["c_star_theorem"].is_null(),
        "divergent extraction must not cite c_star theorem"
    );
    assert_eq!(
        bundle["lean"]["divergence"]["expected_sha256"],
        expected_hash
    );
    assert_eq!(bundle["lean"]["divergence"]["actual_sha256"], actual_hash);
    assert_eq!(
        bundle["lean"]["divergence"]["expected_nodes"],
        expected_nodes
    );
    assert_eq!(bundle["lean"]["divergence"]["actual_nodes"], actual_nodes);
    assert_eq!(
        bundle["capability_threshold"]["c_star_value_proved_on"],
        "unavailable_for_divergent_extraction"
    );
    assert!(
        bundle["capability_threshold"]["c_star"].is_null(),
        "divergent extraction must not emit capability_threshold.c_star"
    );
    assert!(
        bundle["capability_threshold"]["delta"].is_null(),
        "divergent extraction must not emit capability_threshold.delta"
    );
    assert!(
        bundle["capability_threshold"]["computed_from"]
            .as_str()
            .unwrap()
            .contains("extracted graph diverged from committed fixture; no finite Lean fixture theorem applies")
    );
}

#[test]
fn source_path_provenance_distinguishes_identical_fixture_copies() {
    let copied_fixture = temp_fixture_copy("examples/codex-cli-fixture", "source-path-provenance");
    let original = audit_agent_bundle("codex-cli", "examples/codex-cli-fixture");
    let copied = audit_agent_bundle("codex-cli", copied_fixture.to_str().unwrap());

    assert_ne!(
        original, copied,
        "different source paths with identical recognized content must not produce byte-identical bundles"
    );
    assert_eq!(
        original["provenance"]["source_path"],
        fs::canonicalize("examples/codex-cli-fixture")
            .unwrap()
            .display()
            .to_string()
    );
    assert_eq!(
        copied["provenance"]["source_path"],
        fs::canonicalize(&copied_fixture)
            .unwrap()
            .display()
            .to_string()
    );

    let mut normalized_original = original.clone();
    let mut normalized_copied = copied.clone();
    normalized_original["provenance"]["source_path"] = Value::String("<source-path>".to_string());
    normalized_copied["provenance"]["source_path"] = Value::String("<source-path>".to_string());
    assert_eq!(
        normalized_original, normalized_copied,
        "copied fixture bundle should differ only in provenance.source_path"
    );

    fs::remove_dir_all(copied_fixture).unwrap();
}

#[test]
fn divergent_extraction_degrades_theorem_citation_to_diagnostic_only() {
    let codex_fixture = temp_fixture_copy("examples/codex-cli-fixture", "codex-divergent");
    fs::remove_file(codex_fixture.join("stop.rs")).unwrap();
    assert_divergent_extraction_is_diagnostic_only(
        "codex-cli",
        &codex_fixture,
        "examples/codex-cli-fixture",
        "examples/graphs/codex-graph.json",
    );
    fs::remove_dir_all(codex_fixture).unwrap();

    let sdk_fixture = temp_fixture_copy(
        "examples/claude-agent-sdk-fixture",
        "claude-agent-sdk-divergent",
    );
    fs::remove_file(sdk_fixture.join("claude_agent_sdk/types.py")).unwrap();
    assert_divergent_extraction_is_diagnostic_only(
        "claude-agent-sdk",
        &sdk_fixture,
        "examples/claude-agent-sdk-fixture",
        "examples/graphs/claude-agent-sdk-graph.json",
    );
    fs::remove_dir_all(sdk_fixture).unwrap();

    let claude_code_fixture =
        temp_fixture_copy("examples/claude-code-fixture", "claude-code-divergent");
    let claude_code_surface = claude_code_fixture.join("claude_code/public_governance_surface.py");
    let surface = fs::read_to_string(&claude_code_surface).unwrap();
    let perturbed = surface.replace("    \"Stop\": [stop_continuation],\n", "");
    assert_ne!(
        surface, perturbed,
        "Claude Code perturbation must edit the fixture"
    );
    fs::write(claude_code_surface, perturbed).unwrap();
    assert_divergent_extraction_is_diagnostic_only(
        "claude-code",
        &claude_code_fixture,
        "examples/claude-code-fixture",
        "examples/graphs/claude-code-graph.json",
    );
    fs::remove_dir_all(claude_code_fixture).unwrap();
}

#[test]
fn codex_fixture_extracts_to_committed_graph() {
    assert_fixture_extracts_to_committed_graph(
        "examples/codex-cli-fixture",
        "examples/graphs/codex-graph.json",
    );
}

#[test]
fn claude_agent_sdk_fixture_extracts_to_committed_graph() {
    assert_fixture_extracts_to_committed_graph(
        "examples/claude-agent-sdk-fixture",
        "examples/graphs/claude-agent-sdk-graph.json",
    );
}

#[test]
fn claude_code_fixture_extracts_to_committed_graph() {
    assert_fixture_extracts_to_committed_graph(
        "examples/claude-code-fixture",
        "examples/graphs/claude-code-graph.json",
    );
}

#[test]
fn audit_agent_emitted_graphs_text_match_lean_fixture_constant() {
    assert_audit_agent_graph_text_matches_lean_fixture_constant(
        "codex-cli",
        "examples/codex-cli-fixture",
        "examples/graphs/codex-graph.json",
        "lean/Legitimacy/Results/CodexAdmissibilityAudit.lean",
        "codexHooksExtractedGovernanceGraph",
        &[
            "codexExtractedGraphCardinalityAndCStar",
            "codexCliRejectionAndThresholdFacts",
        ],
    );
    assert_audit_agent_graph_text_matches_lean_fixture_constant(
        "claude-agent-sdk",
        "examples/claude-agent-sdk-fixture",
        "examples/graphs/claude-agent-sdk-graph.json",
        "lean/Legitimacy/Results/ClaudeAgentSDKAdmissibilityAudit.lean",
        "claudeAgentSDKHooksExtractedGovernanceGraph",
        &[
            "claudeAgentSdkExtractedGraphCardinalityAndCStar",
            "claudeAgentSdkRejectionAndThresholdFacts",
        ],
    );
    assert_audit_agent_graph_text_matches_lean_fixture_constant(
        "claude-code",
        "examples/claude-code-fixture",
        "examples/graphs/claude-code-graph.json",
        "lean/Legitimacy/Results/ClaudeCodeAdmissibilityAudit.lean",
        "claudeCodeHooksExtractedGovernanceGraph",
        &[
            "claudeCodeExtractedGraphCardinalityAndCStar",
            "claudeCodeCliRejectionAndThresholdFacts",
        ],
    );
}

#[test]
fn audit_agent_runs_codex_fixture_and_emits_evidence_bundle() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "codex-cli", "examples/codex-cli-fixture"])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "rejected codex audit-agent verdict should exit non-zero: {output:?}"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["target"], "codex-cli");
    assert_eq!(bundle["verdict"]["kind"], "rejected");
    assert_eq!(bundle["provenance"]["mode"], "extract");
    assert_binary_version_matches_package(&bundle);
    assert_eq!(
        bundle["provenance"]["extracted_graph_sha256"],
        extracted_graph_hash("examples/codex-cli-fixture")
    );
    assert!(
        bundle["provenance"].get("committed_graph_sha256").is_none(),
        "extract mode should not emit committed_graph_sha256"
    );
    assert!(
        bundle["provenance"].get("committed_graph_commit").is_none(),
        "extract mode should not emit committed_graph_commit"
    );
    assert!(
        bundle.get("replayed_governance_graph").is_none(),
        "extract mode should not emit replayed_governance_graph"
    );
    assert_eq!(
        bundle["extracted_governance_graph"],
        extracted_graph_value("examples/codex-cli-fixture")
    );
    assert_eq!(
        bundle["lean"]["monotonicity_theorem"],
        "codexHooksGovernanceAdmissibilityRejectsMonotonicity"
    );
    assert_committed_fixture_theorems_apply(&bundle);
    assert_eq!(
        bundle["lean"]["module"],
        "Legitimacy.CaseStudies.CodexHarness"
    );
    assert_eq!(
        bundle["lean"]["file_path"],
        "lean/Legitimacy/CaseStudies/CodexHarness.lean"
    );
    assert_graph_cardinality_with_c_star_field(&bundle, "codexExtractedGraphCardinalityAndCStar");
    assert_eq!(bundle["capability_threshold"]["c_star"], "1/10");
    assert_capability_threshold_labels_carrier_and_extracted_context(
        &bundle,
        "codexHarnessDerived_C_star_value on codexHarnessDerivedSpectralGraph: GovGraph ℚ 16 (derived from extracted graph; disconnected, 8 components)",
        "derived from the committed extracted graph",
    );
}

#[test]
fn audit_agent_replay_mode_runs_codex_fixture_and_emits_evidence_bundle() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "codex-cli", "--mode", "replay-committed"])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "rejected codex replay audit-agent verdict should exit non-zero: {output:?}"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["target"], "codex-cli");
    assert_eq!(bundle["verdict"]["kind"], "rejected");
    assert_eq!(bundle["provenance"]["mode"], "replay-committed");
    assert_binary_version_matches_package(&bundle);
    assert_eq!(
        bundle["provenance"]["committed_graph_sha256"],
        committed_fixture_hash("examples/graphs/codex-graph.json")
    );
    assert!(
        bundle["provenance"].get("extracted_graph_sha256").is_none(),
        "replay mode should not emit extracted_graph_sha256"
    );
    assert!(
        bundle.get("extracted_governance_graph").is_none(),
        "replay mode should not emit extracted_governance_graph"
    );
    assert_eq!(
        bundle["replayed_governance_graph"],
        committed_graph_value("examples/graphs/codex-graph.json")
    );
    assert_eq!(
        bundle["provenance"]["committed_graph_path"],
        "examples/graphs/codex-graph.json"
    );
    assert_eq!(
        bundle["provenance"]["committed_graph_commit"],
        committed_fixture_commit("examples/graphs/codex-graph.json")
    );
    assert_eq!(
        bundle["verdict"]["reason"]["named_feature"],
        "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
    );
    assert!(
        bundle["provenance"]["statement"]
            .as_str()
            .unwrap()
            .contains("NOT the result of running extraction on --source-path")
    );
    assert_eq!(
        bundle["lean"]["monotonicity_theorem"],
        "codexHooksGovernanceAdmissibilityRejectsMonotonicity"
    );
    assert_committed_fixture_theorems_apply(&bundle);
    assert_eq!(
        bundle["lean"]["module"],
        "Legitimacy.CaseStudies.CodexHarness"
    );
    assert_eq!(
        bundle["lean"]["file_path"],
        "lean/Legitimacy/CaseStudies/CodexHarness.lean"
    );
    assert_eq!(bundle["capability_threshold"]["c_star"], "1/10");
    assert!(
        bundle["activation_gate"]["refusal"]
            .as_str()
            .unwrap()
            .contains("DeclaredSacrifice")
    );
}

#[test]
fn audit_agent_uses_canonical_named_feature_in_extract_and_replay_modes() {
    let extract = audit_agent_bundle("codex-cli", "examples/codex-cli-fixture");
    let replay_output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "codex-cli", "--mode", "replay-committed"])
        .output()
        .unwrap();
    assert!(!replay_output.status.success());
    let replay: Value = serde_json::from_slice(&replay_output.stdout).unwrap();

    assert_eq!(
        extract["verdict"]["reason"]["named_feature"],
        replay["verdict"]["reason"]["named_feature"]
    );
    assert!(
        extract.get("graph_named_feature").is_none(),
        "extract mode should not emit duplicate graph_named_feature"
    );
    assert!(
        replay.get("graph_named_feature").is_none(),
        "replay mode should not emit duplicate graph_named_feature"
    );
}

#[test]
fn audit_agent_runs_claude_agent_sdk_fixture_and_emits_evidence_bundle() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args([
            "--target",
            "claude-agent-sdk",
            "examples/claude-agent-sdk-fixture",
        ])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "rejected claude-agent-sdk audit-agent verdict should exit non-zero: {output:?}"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["target"], "claude-agent-sdk");
    assert_eq!(bundle["verdict"]["kind"], "rejected");
    assert_eq!(bundle["provenance"]["mode"], "extract");
    assert_eq!(
        bundle["provenance"]["extracted_graph_sha256"],
        extracted_graph_hash("examples/claude-agent-sdk-fixture")
    );
    assert!(
        bundle.get("replayed_governance_graph").is_none(),
        "extract mode should not emit replayed_governance_graph"
    );
    assert_eq!(
        bundle["extracted_governance_graph"],
        extracted_graph_value("examples/claude-agent-sdk-fixture")
    );
    assert_eq!(
        bundle["lean"]["monotonicity_theorem"],
        "claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity"
    );
    assert_committed_fixture_theorems_apply(&bundle);
    assert_eq!(
        bundle["lean"]["module"],
        "Legitimacy.CaseStudies.ClaudeAgentSdkHarness"
    );
    assert_eq!(
        bundle["lean"]["file_path"],
        "lean/Legitimacy/CaseStudies/ClaudeAgentSdkHarness.lean"
    );
    assert_graph_cardinality_with_c_star_field(
        &bundle,
        "claudeAgentSdkExtractedGraphCardinalityAndCStar",
    );
    assert_eq!(bundle["capability_threshold"]["c_star"], "1/10");
    assert_capability_threshold_labels_carrier_and_extracted_context(
        &bundle,
        "claudeAgentSdkHarnessDerived_C_star_value on claudeAgentSdkHarnessDerivedSpectralGraph: GovGraph ℚ 22 (derived from extracted graph; disconnected, 8 K₂ pairs + 6 isolated nodes)",
        "derived from the committed extracted graph",
    );
}

#[test]
fn audit_agent_runs_claude_code_fixture_and_emits_evidence_bundle() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "claude-code", "examples/claude-code-fixture"])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "rejected claude-code audit-agent verdict should exit non-zero: {output:?}"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["target"], "claude-code");
    assert_eq!(bundle["verdict"]["kind"], "rejected");
    assert_eq!(bundle["provenance"]["mode"], "extract");
    assert_eq!(
        bundle["provenance"]["extracted_graph_sha256"],
        extracted_graph_hash("examples/claude-code-fixture")
    );
    assert!(
        bundle.get("replayed_governance_graph").is_none(),
        "extract mode should not emit replayed_governance_graph"
    );
    assert_eq!(
        bundle["extracted_governance_graph"],
        extracted_graph_value("examples/claude-code-fixture")
    );
    assert_eq!(
        bundle["lean"]["theorem_class"],
        "claudeCodeCliRejectionAndThresholdFacts"
    );
    assert_eq!(
        bundle["lean"]["monotonicity_theorem"],
        "claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity"
    );
    assert_eq!(
        bundle["lean"]["c_star_theorem"],
        "claudeCodeHarnessDerived_C_star_value"
    );
    assert_committed_fixture_theorems_apply(&bundle);
    assert_eq!(
        bundle["lean"]["module"],
        "Legitimacy.CaseStudies.ClaudeCodeHarness"
    );
    assert_eq!(
        bundle["lean"]["file_path"],
        "lean/Legitimacy/CaseStudies/ClaudeCodeHarness.lean"
    );
    assert_graph_cardinality_with_c_star_field(
        &bundle,
        "claudeCodeExtractedGraphCardinalityAndCStar",
    );
    assert_eq!(bundle["capability_threshold"]["c_star"], "1/10");
    assert_capability_threshold_labels_carrier_and_extracted_context(
        &bundle,
        "claudeCodeHarnessDerived_C_star_value on claudeCodeHarnessDerivedSpectralGraph: GovGraph ℚ 31 (derived from extracted graph; disconnected, 14 K₂ pairs + 3 isolated nodes)",
        "derived from the committed extracted graph",
    );
}

#[test]
fn audit_agent_replay_mode_runs_claude_code_fixture_and_emits_evidence_bundle() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "claude-code", "--mode", "replay-committed"])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "rejected claude-code replay audit-agent verdict should exit non-zero: {output:?}"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["target"], "claude-code");
    assert_eq!(bundle["verdict"]["kind"], "rejected");
    assert_eq!(bundle["provenance"]["mode"], "replay-committed");
    assert_eq!(
        bundle["provenance"]["committed_graph_sha256"],
        committed_fixture_hash("examples/graphs/claude-code-graph.json")
    );
    assert!(
        bundle.get("extracted_governance_graph").is_none(),
        "replay mode should not emit extracted_governance_graph"
    );
    assert_eq!(
        bundle["replayed_governance_graph"],
        committed_graph_value("examples/graphs/claude-code-graph.json")
    );
    assert_eq!(
        bundle["provenance"]["committed_graph_path"],
        "examples/graphs/claude-code-graph.json"
    );
    assert_eq!(
        bundle["provenance"]["committed_graph_commit"],
        committed_fixture_commit("examples/graphs/claude-code-graph.json")
    );
}

#[test]
fn audit_agent_replay_mode_runs_claude_agent_sdk_fixture_and_emits_evidence_bundle() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "claude-agent-sdk", "--mode", "replay-committed"])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "rejected claude-agent-sdk replay audit-agent verdict should exit non-zero: {output:?}"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["target"], "claude-agent-sdk");
    assert_eq!(bundle["verdict"]["kind"], "rejected");
    assert_eq!(bundle["provenance"]["mode"], "replay-committed");
    assert_eq!(
        bundle["provenance"]["committed_graph_sha256"],
        committed_fixture_hash("examples/graphs/claude-agent-sdk-graph.json")
    );
    assert!(
        bundle.get("extracted_governance_graph").is_none(),
        "replay mode should not emit extracted_governance_graph"
    );
    assert_eq!(
        bundle["replayed_governance_graph"],
        committed_graph_value("examples/graphs/claude-agent-sdk-graph.json")
    );
    assert_eq!(
        bundle["provenance"]["committed_graph_path"],
        "examples/graphs/claude-agent-sdk-graph.json"
    );
    assert_eq!(
        bundle["provenance"]["committed_graph_commit"],
        committed_fixture_commit("examples/graphs/claude-agent-sdk-graph.json")
    );
    assert_eq!(
        bundle["lean"]["monotonicity_theorem"],
        "claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity"
    );
    assert_committed_fixture_theorems_apply(&bundle);
    assert_eq!(
        bundle["lean"]["file_path"],
        "lean/Legitimacy/CaseStudies/ClaudeAgentSdkHarness.lean"
    );
    assert_eq!(bundle["capability_threshold"]["c_star"], "1/10");
}

#[test]
fn audit_agent_extract_mode_emits_independently_extracted_codex_graph() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "codex-cli", "examples/codex-cli-fixture"])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "extract-mode codex audit-agent verdict should exit non-zero: {output:?}"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["target"], "codex-cli");
    assert_eq!(bundle["provenance"]["mode"], "extract");
    assert_eq!(
        bundle["extracted_governance_graph"],
        extracted_graph_value("examples/codex-cli-fixture")
    );
    assert_ne!(
        bundle["lean"]["theorem_class"],
        "unavailable_for_extract_mode"
    );
}

#[test]
fn audit_agent_extract_mode_emits_independently_extracted_claude_agent_sdk_graph() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args([
            "--target",
            "claude-agent-sdk",
            "examples/claude-agent-sdk-fixture",
        ])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "extract-mode claude-agent-sdk audit-agent verdict should exit non-zero: {output:?}"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["target"], "claude-agent-sdk");
    assert_eq!(bundle["provenance"]["mode"], "extract");
    assert_eq!(
        bundle["extracted_governance_graph"],
        extracted_graph_value("examples/claude-agent-sdk-fixture")
    );
    assert_ne!(
        bundle["lean"]["theorem_class"],
        "unavailable_for_extract_mode"
    );
}

#[test]
fn audit_agent_replay_mode_does_not_require_source_path() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "codex-cli", "--mode", "replay-committed"])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "replay mode should still emit rejected fixture verdict"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["target"], "codex-cli");
    assert_eq!(bundle["provenance"]["mode"], "replay-committed");
    assert_eq!(
        bundle["source_pointer"]["file"],
        "examples/graphs/codex-graph.json"
    );
}

#[test]
fn audit_agent_extract_mode_refuses_missing_source_path_with_reason_code() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "codex-cli"])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "missing source path should fail closed in extract mode"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["reason_code"], "missing_source_path");
}

#[test]
fn audit_agent_replay_mode_rejects_source_path() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args([
            "--target",
            "codex-cli",
            "--mode",
            "replay-committed",
            "examples/codex-cli-fixture",
        ])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "replay mode should reject a source path"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["reason_code"], "source_path_for_replay_mode");
}

#[test]
fn audit_agent_refuses_unknown_target_with_reason_code() {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy-audit-agent"))
        .args(["--target", "unknown-lab", "examples/codex-cli-fixture"])
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "unknown target should fail closed"
    );
    let bundle: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(bundle["reason_code"], "unknown_target");
}
