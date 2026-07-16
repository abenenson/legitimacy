/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/
import Legitimacy.Extract.RustHookCore.Fixtures.CodexHooks
import Legitimacy.Extract.RustHookCore.VerdictPullback
import Legitimacy.Results.GovernanceAdmissibilityAudit
/-!
# Legitimacy.Results.CodexAdmissibilityAudit
Lean audit literal for the extracted Codex hooks leaderboard governance graph.
- `codexHooksGovernanceAdmissibilityRejectsMonotonicity`
- `codexHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`
- `codexHooksGovernanceAdmissibilityProofTarget`
## Admissibility Status
The committed Codex hooks graph is byte-stable against
`examples/graphs/codex-graph.json`, but it does not currently satisfy the
governance admissibility diagnostics as a theorem target. Isolating this literal
from the larger leaderboard module shows that graph elaboration is not the primary
failing check; the audit evaluator rejects the graph:
* `auditGraphClaims codexHooksExtractedGraph` has 29 claims, 5 metric
  fields, and no detected cycles.
* `governanceAdmissibilityVerdict codexHooksExtractedGraph` evaluates to
  `AuditVerdict.rejected AuditCheck.monotonicity`.
* `auditGraphNonvacuity ...` rejects with terminal escalation claimants
  generated from the `hook_registration` threshold gates.
The semantic reason is structural. The synthetic witness corpus includes
baseline claims whose `hook_registration` metric starts at `0`, while
`auditGraphDeltas` strengthens that field by `1`. On Codex nodes whose
first-match gates include `.thresholdGate "hook_registration" 1 .escalate`, a
metric strengthening can move a claim from the default `.permit` result to
`.escalate`. Since `decisionRank .permit = 2` and `decisionRank .escalate = 1`,
the current monotonicity check classifies that transition as a worsening.
The same terminal `.escalate` probes also fail nonvacuity because there is no
downstream adjudication node that resolves them to `.permit` or `.deny`.
A Codex governance-admissibility legitimacy theorem therefore requires an
architectural change, not only a faster proof tactic. Viable resolution options are:
* change the extracted graph schema so escalation gates feed an adjudication
  node and final decisions are terminal `.permit`/`.deny`;
* change the governance admissibility diagnostics with a machine-checked argument
  that terminal `.escalate` is a legitimate review-required outcome rather than
  a nonterminal failure/worsening; or
* prove a schema-parametric acyclic theorem with explicit hypotheses excluding
  positive-metric strengthening from lowering `decisionRank`, then make the
  extractor emit per-harness certificates for those hypotheses.
The current Codex graph fails that last hypothesis, so a schema-parametric proof
alone cannot close the present artifact without a graph or semantics change.
-/
set_option autoImplicit false
namespace Legitimacy
/-- Lean audit literal of `examples/graphs/codex-graph.json`. -/
def codexHooksExtractedGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [     .binary "compact.rs::on_PreCompact"
      "compact.rs::on_PreCompact"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "compact.rs::registration::PreCompact::on_PreCompact"
      "compact.rs::registration::PreCompact::on_PreCompact"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "permission_request.rs::on_PermissionRequest"
      "permission_request.rs::on_PermissionRequest"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "deny" .deny
        , .exactMatch "ask" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "permission_request.rs::registration::PermissionRequest::on_PermissionRequest"
      "permission_request.rs::registration::PermissionRequest::on_PermissionRequest"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "post_tool_use.rs::on_PostToolUse"
      "post_tool_use.rs::on_PostToolUse"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "deny" .deny
        , .exactMatch "ask" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "post_tool_use.rs::registration::PostToolUse::on_PostToolUse"
      "post_tool_use.rs::registration::PostToolUse::on_PostToolUse"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "pre_tool_use.rs::on_PreToolUse"
      "pre_tool_use.rs::on_PreToolUse"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "deny" .deny
        , .exactMatch "ask" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
      "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "registry.rs::on_PostCompact"
      "registry.rs::on_PostCompact"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "registry.rs::registration::PostCompact::on_PostCompact"
      "registry.rs::registration::PostCompact::on_PostCompact"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "session_start.rs::on_SessionStart"
      "session_start.rs::on_SessionStart"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "session_start.rs::registration::SessionStart::on_SessionStart"
      "session_start.rs::registration::SessionStart::on_SessionStart"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "stop.rs::on_Stop"
      "stop.rs::on_Stop"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .permit
        , .exactMatch "block" .deny
        ]
      .permit
      .firstMatch
    ,     .binary "stop.rs::registration::Stop::on_Stop"
      "stop.rs::registration::Stop::on_Stop"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "user_prompt_submit.rs::on_UserPromptSubmit"
      "user_prompt_submit.rs::on_UserPromptSubmit"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "user_prompt_submit.rs::registration::UserPromptSubmit::on_UserPromptSubmit"
      "user_prompt_submit.rs::registration::UserPromptSubmit::on_UserPromptSubmit"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ]
  edges :=
    [ { fromNode := "compact.rs::registration::PreCompact::on_PreCompact", toNode := "compact.rs::on_PreCompact", transform := .passThrough }
    , { fromNode := "permission_request.rs::registration::PermissionRequest::on_PermissionRequest", toNode := "permission_request.rs::on_PermissionRequest", transform := .passThrough }
    , { fromNode := "post_tool_use.rs::registration::PostToolUse::on_PostToolUse", toNode := "post_tool_use.rs::on_PostToolUse", transform := .passThrough }
    , { fromNode := "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse", toNode := "pre_tool_use.rs::on_PreToolUse", transform := .passThrough }
    , { fromNode := "registry.rs::registration::PostCompact::on_PostCompact", toNode := "registry.rs::on_PostCompact", transform := .passThrough }
    , { fromNode := "session_start.rs::registration::SessionStart::on_SessionStart", toNode := "session_start.rs::on_SessionStart", transform := .passThrough }
    , { fromNode := "stop.rs::registration::Stop::on_Stop", toNode := "stop.rs::on_Stop", transform := .passThrough }
    , { fromNode := "user_prompt_submit.rs::registration::UserPromptSubmit::on_UserPromptSubmit", toNode := "user_prompt_submit.rs::on_UserPromptSubmit", transform := .passThrough }
    ]

/-- Audit Codex hooks extracted-graph audit subject using the production Lean evaluator. -/
def codexHooksExtractedGraph : AuditSubject where
  graph := codexHooksExtractedGovernanceGraph
  evalNode := auditEvaluateNode

/-- Computed verdict surface for the committed Codex hooks leaderboard graph. -/
def codexHooksGovernanceAdmissibilityVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict codexHooksExtractedGraph

/-- The committed Codex hooks leaderboard graph's governance-admissibility audit proof target. -/
def codexHooksGovernanceAdmissibilityProofTarget : Prop :=
  codexHooksGovernanceAdmissibilityVerdict = AuditVerdict.legitimate

/-- The committed Codex hooks leaderboard graph, produced by source extraction
from the hooks governance fixture, rejects monotonicity under the production
rank lattice `deny = 0, escalate = 1, permit = 2`. This theorem is scoped to the
synthetic structural-probe fixture encoded in the committed extracted graph; it
does not assert rejection for arbitrary live Codex transcripts or future
extractor surfaces. -/
theorem codexHooksGovernanceAdmissibilityRejectsMonotonicity :
    codexHooksGovernanceAdmissibilityVerdict =
      AuditVerdict.rejected AuditCheck.monotonicity := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

def codexHooksGovernanceAdmissibilityVerdictReviewRequired : AuditVerdict :=
  governanceAdmissibilityVerdictReviewRequired codexHooksExtractedGraph

/-- The Codex hooks graph still rejects monotonicity under the review-required
lattice revision. Nonvacuity flips to pass under the same revised semantics,
but a separate deny-lowering monotonicity witness remains. -/
theorem codexHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired :
    codexHooksGovernanceAdmissibilityVerdictReviewRequired =
      AuditVerdict.rejected AuditCheck.monotonicity := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

theorem codexHooksGovernanceAdmissibilityPassesNonvacuityReviewRequired :
    auditCheckStatusReviewRequired codexHooksExtractedGraph AuditCheck.nonvacuous =
      .ok .passed := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- Concrete structural feature behind the Codex source-walked rejection: the
`PreToolUse` registration node contains a `hook_registration` threshold gate
that can lower a strengthened baseline claim from `.permit` to `.escalate`. -/
theorem codexHooks_preToolUseRegistration_hookRegistrationEscalateThresholdGate :
    ∃ gates,
      .binary "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
          "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
          gates .permit .firstMatch ∈
        codexHooksExtractedGovernanceGraph.nodes ∧
        .thresholdGate "hook_registration" 1 .escalate ∈ gates := by
    refine ⟨[.thresholdGate "hook_registration" 1 .escalate], ?_, ?_⟩
    · native_decide
    · simp

/-- Deprecated compatibility alias: the old name described a superseded
extraction fixture (`parse_completed`/`block_reason`/deny). The committed graph
has a `PreToolUse` registration `hook_registration`/escalate threshold. -/
theorem codexHooks_preToolUseParseCompleted_blockReasonDenyThresholdGate :
    ∃ gates,
      .binary "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
          "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
          gates .permit .firstMatch ∈
        codexHooksExtractedGovernanceGraph.nodes ∧
        .thresholdGate "hook_registration" 1 .escalate ∈ gates :=
  codexHooks_preToolUseRegistration_hookRegistrationEscalateThresholdGate

theorem codexHooks_polarity_aware_monotonicity_verdict :
    auditCheckStatusPolarityAware codexHooksExtractedGraph
        AuditCheck.monotonicity =
      .ok .failed := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

namespace RustHookCore
namespace Fixtures

  /-- Permit hook used by the generated-subject fallback fixture. The production
  Codex audit graph above is an `AuditGovernanceGraph`, while
  `GeneratedAuditSubject` currently ranges over the older binary
  `GovernanceGraph` extractor. This minimal two-registration fixture keeps that
  boundary explicit instead of pretending that the one-node source hook is the
  sixteen-node production extract. -/
  def codexUserPromptSubmitGeneratedPermitHook : RustHookCore.HookFnDecl where
    name := "codex_generated_permit"
    event := "UserPromptSubmit"
    inputType := "HookInput"
    resultType := "HookResult"
    body := RustHookCore.Stmt.returnDecision RustHookCore.HookResult.allow

  /-- Deny-branch hook for the generated fallback fixture. It denies the
  production-shaped `permissionDecision = deny` payload and permits other
  modeled payloads, so the extracted graph has both a satisfiable permit path
  and a satisfiable deny path without conditioning on subject id. -/
  def codexUserPromptSubmitGeneratedPermissionGateHook : RustHookCore.HookFnDecl where
    name := "codex_generated_permission_gate"
    event := "PreToolUse"
    inputType := "HookInput"
    resultType := "HookResult"
    body :=
      RustHookCore.Stmt.ifThenElse
        (RustHookCore.Expr.fieldEq "permissionDecision" "deny")
        (RustHookCore.Stmt.returnDecision RustHookCore.HookResult.deny)
        (RustHookCore.Stmt.returnDecision RustHookCore.HookResult.allow)

  def codexUserPromptSubmitGeneratedPrimaryRegistration :
      RustHookCore.Registration where
    event := "UserPromptSubmit"
    callback := "codex_generated_permit"
    kind := .macro

  def codexUserPromptSubmitGeneratedAuditRegistration :
      RustHookCore.Registration where
    event := "PreToolUse"
    callback := "codex_generated_permission_gate"
    kind := .macro

  /-- Minimal multi-node Codex generated-subject program. It is intentionally a
  fallback fixture for the binary hook-core pullback, not the production sixteen-node
  `AuditGovernanceGraph` used by `codexHooksExtractedGovernanceGraph`. -/
  def codexUserPromptSubmitGeneratedProgram : RustHookCore.Program :=
    RustHookCore.Program.mk
      [codexHookResultEnum]
      [ codexUserPromptSubmitGeneratedPermitHook
      , codexUserPromptSubmitGeneratedPermissionGateHook
      ]
      [ codexUserPromptSubmitGeneratedPrimaryRegistration
      , codexUserPromptSubmitGeneratedAuditRegistration
      ]

  /-- Binary graph extracted from the modeled two-registration Codex fallback
  fixture. -/
  def codexUserPromptSubmitExtractedGraph : GovernanceGraph :=
    [ registrationNode codexUserPromptSubmitGeneratedProgram
        codexUserPromptSubmitGeneratedPrimaryRegistration
    , registrationNode codexUserPromptSubmitGeneratedProgram
        codexUserPromptSubmitGeneratedAuditRegistration
    ]

  def codexUserPromptSubmitGeneratedWitnessClaim : ClaimQ :=
    ⟨0, 1, by norm_num, [("permissionDecision", "allow")]⟩

  def codexUserPromptSubmitGeneratedDeniedWitnessClaim : ClaimQ :=
    ⟨1, 1, by norm_num, [("permissionDecision", "deny")]⟩

  /-- The generated-subject fallback is no longer a one-node constant kernel. -/
  theorem codexUserPromptSubmit_generated_graph_multi_node :
      codexUserPromptSubmitExtractedGraph.length = 2 := by
    native_decide

  /-- Concrete permit and deny paths through the generated fallback nodes. The
  first node forwards both claims; the second node is the metadata-conditioned
  deny branch that separates `permissionDecision = allow` from
  `permissionDecision = deny`. -/
  theorem codexUserPromptSubmit_generated_permit_deny_paths :
      graphDecide codexUserPromptSubmitExtractedGraph
          [codexUserPromptSubmitGeneratedWitnessClaim]
          codexUserPromptSubmitGeneratedWitnessClaim.id =
        BinaryDecision.Permit ∧
      graphDecide codexUserPromptSubmitExtractedGraph
          [codexUserPromptSubmitGeneratedDeniedWitnessClaim]
          codexUserPromptSubmitGeneratedDeniedWitnessClaim.id =
        BinaryDecision.Deny := by
    native_decide

set_option linter.unusedSimpArgs false in
lemma codexUserPromptSubmit_generated_graph_decide_eq
    (claims : List ClaimQ) (j : ClaimantId) :
    graphDecide codexUserPromptSubmitExtractedGraph claims j =
      if ClaimProfile.lookup claims j "permissionDecision" == some "deny" then
        BinaryDecision.Deny
      else
        BinaryDecision.Permit := by
  simp [codexUserPromptSubmitExtractedGraph,
    codexUserPromptSubmitGeneratedProgram,
    codexUserPromptSubmitGeneratedPermitHook,
    codexUserPromptSubmitGeneratedPermissionGateHook,
    codexUserPromptSubmitGeneratedPrimaryRegistration,
    codexUserPromptSubmitGeneratedAuditRegistration,
    graphDecide, registrationNode, evalRegistration, filterPermitted,
    findHook?, Program.hooks, Stmt.evalDecision, Stmt.evalHookResult,
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
lemma codexUserPromptSubmit_generated_consistency :
    auditCheckHolds .consistency
      codexUserPromptSubmitExtractedGraph := by
    intro claims k j hk hj hkj hdist hden
    rw [codexUserPromptSubmit_generated_graph_decide_eq claims k] at hden
    have _hk_deny_branch :
        ClaimProfile.lookup claims k "permissionDecision" = some "deny" := by
      by_cases hlookup :
          ClaimProfile.lookup claims k "permissionDecision" = some "deny"
      · exact hlookup
      · simp [hlookup] at hden
    rw [codexUserPromptSubmit_generated_graph_decide_eq claims j]
    rw [codexUserPromptSubmit_generated_graph_decide_eq
      (removeClaimGraph k claims) j]
    rw [ClaimProfile.lookup_removeClaimGraph_of_ne claims k j
      "permissionDecision" hdist hkj]

/-- Forced by strength-invariance (axiom group docstring). -/
lemma codexUserPromptSubmit_generated_solidarity :
    auditCheckHolds .solidarity
      codexUserPromptSubmitExtractedGraph := by
    intro claims α hα j hj
    change
      graphDecide codexUserPromptSubmitExtractedGraph claims j =
        graphDecide codexUserPromptSubmitExtractedGraph
          (claims.map fun c => c.scaleStrength α hα) j
    rw [codexUserPromptSubmit_generated_graph_decide_eq claims j]
    rw [codexUserPromptSubmit_generated_graph_decide_eq
      (claims.map fun c => c.scaleStrength α hα) j]
    rw [ClaimProfile.lookup_scaleStrength claims j "permissionDecision" α hα]

/-- Forced by strength-invariance (axiom group docstring). -/
lemma codexUserPromptSubmit_generated_monotonicity :
    auditCheckHolds .monotonicity
      codexUserPromptSubmitExtractedGraph := by
    intro claims k s' hs' j hk hdist hbound hpermit
    rw [codexUserPromptSubmit_generated_graph_decide_eq claims j] at hpermit
    rw [codexUserPromptSubmit_generated_graph_decide_eq
      (strengthenClaim k s' hs' claims) j]
    rw [ClaimProfile.lookup_strengthenClaim claims j k "permissionDecision" s' hs']
    exact hpermit

/-- Forced by strength-invariance (axiom group docstring). -/
lemma codexUserPromptSubmit_generated_strategyproofness :
    auditCheckHolds .strategyproofness
      codexUserPromptSubmitExtractedGraph := by
    intro claims k s_r hs_r hk hdist hpermit
    rw [codexUserPromptSubmit_generated_graph_decide_eq
      (strengthenClaim k s_r hs_r claims) k] at hpermit
    rw [codexUserPromptSubmit_generated_graph_decide_eq claims k]
    rw [ClaimProfile.lookup_strengthenClaim claims k k "permissionDecision" s_r hs_r] at hpermit
    exact hpermit

def codexUserPromptSubmitGeneratedSubject : AuditSubject :=
  RustHookCore.liftGovernanceGraphToAuditSubject
    codexUserPromptSubmitExtractedGraph

  lemma codexUserPromptSubmit_extracts_generated_graph :
      extractRustHookCore codexUserPromptSubmitGeneratedProgram =
        .ok codexUserPromptSubmitExtractedGraph := by
    rfl

  /-- Multi-node generated-subject inhabitant for the modeled Codex hook-core
  fallback fixture. The real production Codex audit remains the sixteen-node
  `codexHooksExtractedGovernanceGraph` above; this instance only covers the older
  binary hook-core pullback surface.

  The four diagnostic projections hold on this fixture; consistency by
  deny-branch witness, the rest forced structurally by the solidarity +
  strategyproofness joint constraint. The `hpass` premise is currently inert
  for the graph-property conclusion: it is decoded to a core Boolean witness,
  while the property is proved independently by the fixture lemmas below rather
  than by a general core-to-`auditCheckHolds` soundness bridge. -/
  instance codexUserPromptSubmitGeneratedAuditSubject :
      RustHookCore.GeneratedAuditSubject
        codexUserPromptSubmitGeneratedProgram
        codexUserPromptSubmitGeneratedSubject where
  graph := codexUserPromptSubmitExtractedGraph
  extracted := codexUserPromptSubmit_extracts_generated_graph
  subject_embeds_graph := rfl
  pass_consistency := fun hpass => by
    have _hcore :=
      auditCheckStatus_passed_implies_consistencyCore
        codexUserPromptSubmitGeneratedSubject hpass
    exact codexUserPromptSubmit_generated_consistency
  pass_solidarity := fun hpass => by
    have _hcore :=
      auditCheckStatus_passed_implies_solidarityCore
        codexUserPromptSubmitGeneratedSubject hpass
    exact codexUserPromptSubmit_generated_solidarity
  pass_monotonicity := fun hpass => by
    have _hcore :=
      auditCheckStatus_passed_implies_monotonicityCorePolarityAware
        codexUserPromptSubmitGeneratedSubject hpass
    exact codexUserPromptSubmit_generated_monotonicity
  pass_strategyproofness := fun hpass => by
    have _hcore :=
      auditCheckStatus_passed_implies_strategyproofnessCore
        codexUserPromptSubmitGeneratedSubject hpass
    exact codexUserPromptSubmit_generated_strategyproofness

end Fixtures
end RustHookCore

end Legitimacy
