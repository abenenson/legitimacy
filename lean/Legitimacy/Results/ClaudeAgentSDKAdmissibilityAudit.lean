/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/
import Legitimacy.Extract.PythonHookCore.Fixtures.ClaudeAgentSDK
import Legitimacy.Extract.PythonHookCore.VerdictPullback
import Legitimacy.Results.CodexAdmissibilityAudit
import Legitimacy.Spectral.Capacity.CriticalCapability
/-!
# Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit
Lean audit literal for the extracted Claude Agent SDK hooks leaderboard graph.
The committed graph is byte-stable against
`examples/graphs/claude-agent-sdk-graph.json` and is generated from the
MIT-licensed Python Agent SDK slice, not from proprietary Claude Code runtime
source. The extracted graph rejects monotonicity by the same structural mechanism
recorded for Codex: hook/protocol registration strengthening can move a baseline
claim from default `.permit` to terminal `.escalate`, without downstream runtime
adjudication inside the redistributable SDK slice.
-/
set_option autoImplicit false
namespace Legitimacy
/-- Lean audit literal of `examples/graphs/claude-agent-sdk-graph.json`. -/
def claudeAgentSDKHooksExtractedGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [     .binary "claude_agent_sdk/hooks.py::HookDecision"
      "claude_agent_sdk/hooks.py::HookDecision"
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .escalate
        , .exactMatch "block" .deny
        , .exactMatch "deny" .deny
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::notification_escalation"
      "claude_agent_sdk/hooks.py::notification_escalation"
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::permission_request_review"
      "claude_agent_sdk/hooks.py::permission_request_review"
      [ .exactMatch "deny" .deny
        ]
      .deny
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::post_tool_use_failure_review"
      "claude_agent_sdk/hooks.py::post_tool_use_failure_review"
      [ .exactMatch "block" .deny
        ]
      .deny
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::post_tool_use_observation"
      "claude_agent_sdk/hooks.py::post_tool_use_observation"
      [ .exactMatch "allow" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::pre_tool_use_permission_decision"
      "claude_agent_sdk/hooks.py::pre_tool_use_permission_decision"
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::registration::Notification::notification_escalation"
      "claude_agent_sdk/hooks.py::registration::Notification::notification_escalation"
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::registration::PermissionRequest::permission_request_review"
      "claude_agent_sdk/hooks.py::registration::PermissionRequest::permission_request_review"
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::registration::PostToolUse::post_tool_use_observation"
      "claude_agent_sdk/hooks.py::registration::PostToolUse::post_tool_use_observation"
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::registration::PostToolUseFailure::post_tool_use_failure_review"
      "claude_agent_sdk/hooks.py::registration::PostToolUseFailure::post_tool_use_failure_review"
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::registration::PreToolUse::pre_tool_use_permission_decision"
      "claude_agent_sdk/hooks.py::registration::PreToolUse::pre_tool_use_permission_decision"
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::registration::Stop::stop_continuation"
      "claude_agent_sdk/hooks.py::registration::Stop::stop_continuation"
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::registration::SubagentStart::subagent_start_review"
      "claude_agent_sdk/hooks.py::registration::SubagentStart::subagent_start_review"
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::registration::UserPromptSubmit::user_prompt_submit_guard"
      "claude_agent_sdk/hooks.py::registration::UserPromptSubmit::user_prompt_submit_guard"
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::stop_continuation"
      "claude_agent_sdk/hooks.py::stop_continuation"
      [ .exactMatch "block" .deny
        ]
      .deny
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::subagent_start_review"
      "claude_agent_sdk/hooks.py::subagent_start_review"
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_agent_sdk/hooks.py::user_prompt_submit_guard"
      "claude_agent_sdk/hooks.py::user_prompt_submit_guard"
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_agent_sdk/types.py::PermissionBehavior"
      "claude_agent_sdk/types.py::PermissionBehavior"
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .escalate
        , .exactMatch "deny" .deny
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_agent_sdk/types.py::PermissionResultAllow"
      "claude_agent_sdk/types.py::PermissionResultAllow"
      [ .exactMatch "allow" .permit
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_agent_sdk/types.py::PermissionResultDeny"
      "claude_agent_sdk/types.py::PermissionResultDeny"
      [ .exactMatch "deny" .deny
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_agent_sdk/types.py::PreToolUseHookSpecificOutput"
      "claude_agent_sdk/types.py::PreToolUseHookSpecificOutput"
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .escalate
        , .exactMatch "defer" .escalate
        , .exactMatch "deny" .deny
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_agent_sdk/types.py::SyncHookJSONOutput"
      "claude_agent_sdk/types.py::SyncHookJSONOutput"
      [ .exactMatch "block" .deny
        ]
      .escalate
      .firstMatch
    ]
  edges :=
    [ { fromNode := "claude_agent_sdk/hooks.py::registration::Notification::notification_escalation", toNode := "claude_agent_sdk/hooks.py::notification_escalation", transform := .passThrough }
    , { fromNode := "claude_agent_sdk/hooks.py::registration::PermissionRequest::permission_request_review", toNode := "claude_agent_sdk/hooks.py::permission_request_review", transform := .passThrough }
    , { fromNode := "claude_agent_sdk/hooks.py::registration::PostToolUse::post_tool_use_observation", toNode := "claude_agent_sdk/hooks.py::post_tool_use_observation", transform := .passThrough }
    , { fromNode := "claude_agent_sdk/hooks.py::registration::PostToolUseFailure::post_tool_use_failure_review", toNode := "claude_agent_sdk/hooks.py::post_tool_use_failure_review", transform := .passThrough }
    , { fromNode := "claude_agent_sdk/hooks.py::registration::PreToolUse::pre_tool_use_permission_decision", toNode := "claude_agent_sdk/hooks.py::pre_tool_use_permission_decision", transform := .passThrough }
    , { fromNode := "claude_agent_sdk/hooks.py::registration::Stop::stop_continuation", toNode := "claude_agent_sdk/hooks.py::stop_continuation", transform := .passThrough }
    , { fromNode := "claude_agent_sdk/hooks.py::registration::SubagentStart::subagent_start_review", toNode := "claude_agent_sdk/hooks.py::subagent_start_review", transform := .passThrough }
    , { fromNode := "claude_agent_sdk/hooks.py::registration::UserPromptSubmit::user_prompt_submit_guard", toNode := "claude_agent_sdk/hooks.py::user_prompt_submit_guard", transform := .passThrough }
    ]
/-- Claude Agent SDK hooks extracted-graph audit subject using the production Lean evaluator. -/
def claudeAgentSDKHooksExtractedGraph : AuditSubject where
  graph := claudeAgentSDKHooksExtractedGovernanceGraph
  evalNode := auditEvaluateNode
/-- Computed verdict surface for the committed Claude Agent SDK hooks leaderboard graph. -/
def claudeAgentSDKHooksGovernanceAdmissibilityVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict claudeAgentSDKHooksExtractedGraph



/-- The committed Claude Agent SDK hooks leaderboard graph rejects monotonicity. -/
theorem claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity :
    claudeAgentSDKHooksGovernanceAdmissibilityVerdict =
      AuditVerdict.rejected AuditCheck.monotonicity := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

def claudeAgentSDKHooksGovernanceAdmissibilityVerdictReviewRequired : AuditVerdict :=
  governanceAdmissibilityVerdictReviewRequired claudeAgentSDKHooksExtractedGraph

/-- The refreshed Claude Agent SDK hook graph still rejects monotonicity under
the review-required lattice revision. Nonvacuity flips to pass under the same
revised semantics, but a separate rank-lowering witness remains in the
upstream-grounded hook-registration adapter. -/
theorem claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired :
    claudeAgentSDKHooksGovernanceAdmissibilityVerdictReviewRequired =
      AuditVerdict.rejected AuditCheck.monotonicity := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

theorem claudeAgentSDKHooksGovernanceAdmissibilityPassesNonvacuityReviewRequired :
    auditCheckStatusReviewRequired claudeAgentSDKHooksExtractedGraph AuditCheck.nonvacuous =
      .ok .passed := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- Paired cross-vendor review-required result for the committed extracted hook
governance graphs: both Codex and the refreshed Claude Agent SDK fixture remain
rejected by monotonicity under the review-required lattice. This is a
per-harness theorem over the modeled extracted graphs, not a universal runtime
claim about either provider protocol. -/
theorem codex_claude_sdk_review_required_joint_rejection :
    codexHooksGovernanceAdmissibilityVerdictReviewRequired =
        AuditVerdict.rejected AuditCheck.monotonicity ∧
      claudeAgentSDKHooksGovernanceAdmissibilityVerdictReviewRequired =
        AuditVerdict.rejected AuditCheck.monotonicity :=
  ⟨codexHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired,
    claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired⟩

theorem claudeAgentSDKHooks_polarity_aware_monotonicity_verdict :
    auditCheckStatusPolarityAware claudeAgentSDKHooksExtractedGraph
        AuditCheck.monotonicity =
      .ok .failed := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

namespace PythonHookCore
namespace Fixtures

/-- Permit callback used by the generated-subject fallback fixture. The
production Claude Agent SDK audit graph above is an `AuditGovernanceGraph`,
while `GeneratedAuditSubject` currently ranges over the older binary
`GovernanceGraph` extractor. This minimal two-registration fixture keeps that
boundary explicit instead of pretending that the one-callback source hook is the
twenty-two-node production extract. -/
def claudeAgentSDKPreToolUseGeneratedPermitCallback :
    PythonHookCore.CallbackDecl where
  name := "claude_agent_sdk_generated_permit"
  body := PythonHookCore.Stmt.returnDecision PythonHookCore.HookResult.allow

/-- Deny-branch callback for the generated fallback fixture. It denies the
production-shaped `permissionDecision = deny` payload and permits other modeled
payloads, so the extracted graph has both a satisfiable permit path and a
satisfiable deny path without conditioning on subject id. -/
def claudeAgentSDKPreToolUseGeneratedPermissionGateCallback :
    PythonHookCore.CallbackDecl where
  name := "claude_agent_sdk_generated_permission_gate"
  body :=
    PythonHookCore.Stmt.ifThenElse
      (PythonHookCore.Expr.fieldEq "permissionDecision" "deny")
      (PythonHookCore.Stmt.returnDecision PythonHookCore.HookResult.deny)
      (PythonHookCore.Stmt.returnDecision PythonHookCore.HookResult.allow)

def claudeAgentSDKPreToolUseGeneratedPrimaryRegistration :
    PythonHookCore.Registration where
  hook := "PreToolUse"
  callback := "claude_agent_sdk_generated_permit"

def claudeAgentSDKPreToolUseGeneratedAuditRegistration :
    PythonHookCore.Registration where
  hook := "PostToolUse"
  callback := "claude_agent_sdk_generated_permission_gate"

/-- Minimal multi-node Claude Agent SDK generated-subject program. It is a
fallback fixture for the binary hook-core pullback, not the production
twenty-two-node `AuditGovernanceGraph` used by
`claudeAgentSDKHooksExtractedGovernanceGraph`. -/
def claudeAgentSDKPreToolUseGeneratedProgram : PythonHookCore.Program :=
  PythonHookCore.Program.mk
    [claudeAgentSDKPreToolUseOutputSchema]
    [claudeAgentSDKHookEventDispatch]
    [ claudeAgentSDKPreToolUseGeneratedPermitCallback
    , claudeAgentSDKPreToolUseGeneratedPermissionGateCallback
    ]
    [ claudeAgentSDKPreToolUseGeneratedPrimaryRegistration
    , claudeAgentSDKPreToolUseGeneratedAuditRegistration
    ]

/-- Binary graph extracted from the modeled two-registration Claude SDK fallback
fixture. -/
def claudeAgentSDKPreToolUseExtractedGraph : GovernanceGraph :=
  [ registrationNode claudeAgentSDKPreToolUseGeneratedProgram
      claudeAgentSDKPreToolUseGeneratedPrimaryRegistration
  , registrationNode claudeAgentSDKPreToolUseGeneratedProgram
      claudeAgentSDKPreToolUseGeneratedAuditRegistration
  ]

def claudeAgentSDKPreToolUseGeneratedWitnessClaim : ClaimQ :=
  ⟨0, 1, by norm_num, [("permissionDecision", "allow")]⟩

def claudeAgentSDKPreToolUseGeneratedDeniedWitnessClaim : ClaimQ :=
  ⟨1, 1, by norm_num, [("permissionDecision", "deny")]⟩

/-- The generated-subject fallback is no longer a one-node constant kernel. -/
theorem claudeAgentSDKPreToolUse_generated_graph_multi_node :
    claudeAgentSDKPreToolUseExtractedGraph.length = 2 := by
  native_decide

/-- Concrete permit and deny paths through the generated fallback nodes. The
first node forwards both claims; the second node is the metadata-conditioned
deny branch that separates `permissionDecision = allow` from
`permissionDecision = deny`. -/
theorem claudeAgentSDKPreToolUse_generated_permit_deny_paths :
    graphDecide claudeAgentSDKPreToolUseExtractedGraph
        [claudeAgentSDKPreToolUseGeneratedWitnessClaim]
        claudeAgentSDKPreToolUseGeneratedWitnessClaim.id =
      BinaryDecision.Permit ∧
    graphDecide claudeAgentSDKPreToolUseExtractedGraph
        [claudeAgentSDKPreToolUseGeneratedDeniedWitnessClaim]
        claudeAgentSDKPreToolUseGeneratedDeniedWitnessClaim.id =
      BinaryDecision.Deny := by
  native_decide

set_option linter.unusedSimpArgs false in
lemma claudeAgentSDKPreToolUse_generated_graph_decide_eq
    (claims : List ClaimQ) (j : ClaimantId) :
    graphDecide claudeAgentSDKPreToolUseExtractedGraph claims j =
      if ClaimProfile.lookup claims j "permissionDecision" == some "deny" then
        BinaryDecision.Deny
      else
        BinaryDecision.Permit := by
  simp [claudeAgentSDKPreToolUseExtractedGraph,
    claudeAgentSDKPreToolUseGeneratedProgram,
    claudeAgentSDKPreToolUseGeneratedPermitCallback,
    claudeAgentSDKPreToolUseGeneratedPermissionGateCallback,
    claudeAgentSDKPreToolUseGeneratedPrimaryRegistration,
    claudeAgentSDKPreToolUseGeneratedAuditRegistration,
    graphDecide, registrationNode, evalRegistration, filterPermitted,
    findCallback?, Program.callbacks, Stmt.evalDecision, Stmt.evalHookResult,
    Expr.eval, HookResult.toDecision]
  by_cases hdeny :
      ClaimProfile.lookup claims j "permissionDecision" = some "deny"
  · simp [hdeny]
  · simp [hdeny]

/-!
Monotonicity holds structurally on this fixture: GraphSolidarity quantifies
over all positive scale factors α > 0, and GraphStrategyproofness forbids
verdict gain via strength misreport. The joint constraint forces the verdict to
be strength-invariant. Here the deny condition is metadata-conditioned on the
production-shaped `permissionDecision = deny` field value, not subject-id
conditioned. Consequently, monotonicity (and strategyproofness, and the
strength-dimension of solidarity) close after rewriting through the
graph-decide equation -- this is the axioms doing their work, not a Pattern-1
discharge-discipline escape.
-/

/-- Genuinely consumes the deny premise to expose the structural metadata deny branch. -/
lemma claudeAgentSDKPreToolUse_generated_consistency :
    auditCheckHolds .consistency
      claudeAgentSDKPreToolUseExtractedGraph := by
  intro claims k j hk hj hkj hdist hden
  rw [claudeAgentSDKPreToolUse_generated_graph_decide_eq claims k] at hden
  have _hk_deny_branch :
      ClaimProfile.lookup claims k "permissionDecision" = some "deny" := by
    by_cases hlookup :
        ClaimProfile.lookup claims k "permissionDecision" = some "deny"
    · exact hlookup
    · simp [hlookup] at hden
  rw [claudeAgentSDKPreToolUse_generated_graph_decide_eq claims j]
  rw [claudeAgentSDKPreToolUse_generated_graph_decide_eq
    (removeClaimGraph k claims) j]
  rw [ClaimProfile.lookup_removeClaimGraph_of_ne claims k j
    "permissionDecision" hdist hkj]

/-- Forced by strength-invariance (axiom group docstring). -/
lemma claudeAgentSDKPreToolUse_generated_solidarity :
    auditCheckHolds .solidarity
      claudeAgentSDKPreToolUseExtractedGraph := by
  intro claims α hα j hj
  change
    graphDecide claudeAgentSDKPreToolUseExtractedGraph claims j =
      graphDecide claudeAgentSDKPreToolUseExtractedGraph
        (claims.map fun c => c.scaleStrength α hα) j
  rw [claudeAgentSDKPreToolUse_generated_graph_decide_eq claims j]
  rw [claudeAgentSDKPreToolUse_generated_graph_decide_eq
    (claims.map fun c => c.scaleStrength α hα) j]
  rw [ClaimProfile.lookup_scaleStrength claims j "permissionDecision" α hα]

/-- Forced by strength-invariance (axiom group docstring). -/
lemma claudeAgentSDKPreToolUse_generated_monotonicity :
    auditCheckHolds .monotonicity
      claudeAgentSDKPreToolUseExtractedGraph := by
  intro claims k s' hs' j hk hdist hbound hpermit
  rw [claudeAgentSDKPreToolUse_generated_graph_decide_eq claims j] at hpermit
  rw [claudeAgentSDKPreToolUse_generated_graph_decide_eq
    (strengthenClaim k s' hs' claims) j]
  rw [ClaimProfile.lookup_strengthenClaim claims j k "permissionDecision" s' hs']
  exact hpermit

/-- Forced by strength-invariance (axiom group docstring). -/
lemma claudeAgentSDKPreToolUse_generated_strategyproofness :
    auditCheckHolds .strategyproofness
      claudeAgentSDKPreToolUseExtractedGraph := by
  intro claims k s_r hs_r hk hdist hpermit
  rw [claudeAgentSDKPreToolUse_generated_graph_decide_eq
    (strengthenClaim k s_r hs_r claims) k] at hpermit
  rw [claudeAgentSDKPreToolUse_generated_graph_decide_eq claims k]
  rw [ClaimProfile.lookup_strengthenClaim claims k k "permissionDecision" s_r hs_r] at hpermit
  exact hpermit

def claudeAgentSDKPreToolUseGeneratedSubject : AuditSubject :=
  PythonHookCore.liftGovernanceGraphToAuditSubject
    claudeAgentSDKPreToolUseExtractedGraph

lemma claudeAgentSDKPreToolUse_extracts_generated_graph :
    extractPythonHookCore claudeAgentSDKPreToolUseGeneratedProgram =
      .ok claudeAgentSDKPreToolUseExtractedGraph := by
  rfl

/-- Multi-node generated-subject inhabitant for the modeled Claude SDK hook-core
fallback fixture. The real production SDK audit remains the twenty-two-node
`claudeAgentSDKHooksExtractedGovernanceGraph` above; this instance only covers
the older binary hook-core pullback surface.

The four diagnostic projections hold on this fixture; consistency by
deny-branch witness, the rest forced structurally by the solidarity +
strategyproofness joint constraint. The `hpass` premise is currently inert for
the graph-property conclusion: it is decoded to a core Boolean witness, while
the property is proved independently by the fixture lemmas below rather than by
a general core-to-`auditCheckHolds` soundness bridge. -/
instance claudeAgentSDKPreToolUseGeneratedAuditSubject :
    PythonHookCore.GeneratedAuditSubject
      claudeAgentSDKPreToolUseGeneratedProgram
      claudeAgentSDKPreToolUseGeneratedSubject where
  graph := claudeAgentSDKPreToolUseExtractedGraph
  extracted := claudeAgentSDKPreToolUse_extracts_generated_graph
  subject_embeds_graph := rfl
  pass_consistency := fun hpass => by
    have _hcore :=
      auditCheckStatus_passed_implies_consistencyCore
        claudeAgentSDKPreToolUseGeneratedSubject hpass
    exact claudeAgentSDKPreToolUse_generated_consistency
  pass_solidarity := fun hpass => by
    have _hcore :=
      auditCheckStatus_passed_implies_solidarityCore
        claudeAgentSDKPreToolUseGeneratedSubject hpass
    exact claudeAgentSDKPreToolUse_generated_solidarity
  pass_monotonicity := fun hpass => by
    have _hcore :=
      auditCheckStatus_passed_implies_monotonicityCorePolarityAware
        claudeAgentSDKPreToolUseGeneratedSubject hpass
    exact claudeAgentSDKPreToolUse_generated_monotonicity
  pass_strategyproofness := fun hpass => by
    have _hcore :=
      auditCheckStatus_passed_implies_strategyproofnessCore
        claudeAgentSDKPreToolUseGeneratedSubject hpass
    exact claudeAgentSDKPreToolUse_generated_strategyproofness

end Fixtures
end PythonHookCore

/-- Legacy hand-authored uniform-triangle spectral carrier for the Claude Agent
SDK threshold-rejection bundle, superseded by the derived projection in
`Legitimacy.CaseStudies.ClaudeAgentSdkHarness` and retained for citation
stability. -/
def claudeAgentSdkHarnessSpectralGraph : GovGraph ℚ 3 :=
  uniTriGraph

/-- Legacy hand-authored rank signal for the Claude Agent SDK threshold-
rejection bundle, superseded by the graph-derived failure signal in
`Legitimacy.CaseStudies.ClaudeAgentSdkHarness` and retained for citation
stability. -/
def claudeAgentSdkHarnessFailureSignal : Fin 3 → ℚ :=
  sig

/-- Legacy Claude Agent SDK audit tolerance for the C* threshold; retained as
the tolerance reused by the derived carrier. -/
def claudeAgentSdkHarnessTolerance : ℚ :=
  1 / 10

/-- Exact critical capability value for the legacy hand-authored Claude Agent
SDK carrier: `1/10`. The derived projection proves the same value under
`claudeAgentSdkHarnessDerived_C_star_value`. -/
theorem claudeAgentSdkHarness_C_star_value :
    C_star claudeAgentSdkHarnessSpectralGraph
      claudeAgentSdkHarnessFailureSignal
      claudeAgentSdkHarnessTolerance = 1 / 10 := by
  exact concrete_C_star_values.1

/-- The committed Claude Agent SDK extracted graph has the finite hook surface
used by the v1.0.0 binary evidence bundle. -/
theorem claudeAgentSdkHarness_extracted_node_count :
    claudeAgentSDKHooksExtractedGovernanceGraph.nodes.length = 22 := by
  native_decide

/-- The committed Claude Agent SDK extracted graph has registration-to-callback edges in the extracted SDK hook surface. -/
theorem claudeAgentSdkHarness_extracted_edge_count :
    claudeAgentSDKHooksExtractedGovernanceGraph.edges.length = 8 := by
  native_decide

end Legitimacy
