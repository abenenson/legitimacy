/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit
import Legitimacy.Spectral.Capacity.CriticalCapability

/-!
# Legitimacy.Results.ClaudeCodeAdmissibilityAudit

Lean audit literal for the Claude Code public hook/settings/command governance
surface fixture.

This module is intentionally separate from
`Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit`: the Claude Code public
surface has its own extracted graph (31 nodes / 14 edges) and theorem lane.
-/

set_option autoImplicit false

namespace Legitimacy

/-
Claude Code public hook/settings/command-surface lane. This block is intentionally
not sourced from `claude-agent-sdk-python`; it encodes the public Claude Code
schema fixture under `examples/claude-code-fixture`.
-/

/-- Lean audit literal of `examples/graphs/claude-code-graph.json`, derived from the public Claude Code governance docs. -/
def claudeCodeHooksExtractedGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [     .binary "claude_code/public_governance_surface.py::HookDecision"
      "claude_code/public_governance_surface.py::HookDecision"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .escalate
        , .exactMatch "block" .deny
        , .exactMatch "deny" .deny
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::PermissionDecision"
      "claude_code/public_governance_surface.py::PermissionDecision"
      
      [ .exactMatch "allow" .permit
        , .exactMatch "ask" .escalate
        , .exactMatch "defer" .escalate
        , .exactMatch "deny" .deny
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::StopHookSpecificOutput"
      "claude_code/public_governance_surface.py::StopHookSpecificOutput"
      
      [ .exactMatch "block" .deny
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::config_change_review"
      "claude_code/public_governance_surface.py::config_change_review"
      
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::instructions_loaded_review"
      "claude_code/public_governance_surface.py::instructions_loaded_review"
      
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::notification_review"
      "claude_code/public_governance_surface.py::notification_review"
      
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::permission_request_decision"
      "claude_code/public_governance_surface.py::permission_request_decision"
      
      [ .exactMatch "deny" .deny
        ]
      .deny
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::post_tool_use_observation"
      "claude_code/public_governance_surface.py::post_tool_use_observation"
      
      [ .exactMatch "allow" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::pre_compact_review"
      "claude_code/public_governance_surface.py::pre_compact_review"
      
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::pre_tool_use_permission_decision"
      "claude_code/public_governance_surface.py::pre_tool_use_permission_decision"
      
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::ConfigChange::config_change_review"
      "claude_code/public_governance_surface.py::registration::ConfigChange::config_change_review"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::InstructionsLoaded::instructions_loaded_review"
      "claude_code/public_governance_surface.py::registration::InstructionsLoaded::instructions_loaded_review"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::Notification::notification_review"
      "claude_code/public_governance_surface.py::registration::Notification::notification_review"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::PermissionRequest::permission_request_decision"
      "claude_code/public_governance_surface.py::registration::PermissionRequest::permission_request_decision"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::PostToolUse::post_tool_use_observation"
      "claude_code/public_governance_surface.py::registration::PostToolUse::post_tool_use_observation"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::PreCompact::pre_compact_review"
      "claude_code/public_governance_surface.py::registration::PreCompact::pre_compact_review"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::PreToolUse::pre_tool_use_permission_decision"
      "claude_code/public_governance_surface.py::registration::PreToolUse::pre_tool_use_permission_decision"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::SessionStart::session_start_policy"
      "claude_code/public_governance_surface.py::registration::SessionStart::session_start_policy"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::Setup::setup_policy"
      "claude_code/public_governance_surface.py::registration::Setup::setup_policy"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::Stop::stop_continuation"
      "claude_code/public_governance_surface.py::registration::Stop::stop_continuation"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::SubagentStart::subagent_start_review"
      "claude_code/public_governance_surface.py::registration::SubagentStart::subagent_start_review"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::SubagentStop::subagent_stop_review"
      "claude_code/public_governance_surface.py::registration::SubagentStop::subagent_stop_review"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::UserPromptExpansion::user_prompt_expansion_guard"
      "claude_code/public_governance_surface.py::registration::UserPromptExpansion::user_prompt_expansion_guard"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::registration::UserPromptSubmit::user_prompt_submit_guard"
      "claude_code/public_governance_surface.py::registration::UserPromptSubmit::user_prompt_submit_guard"
      
      [ .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::session_start_policy"
      "claude_code/public_governance_surface.py::session_start_policy"
      
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::setup_policy"
      "claude_code/public_governance_surface.py::setup_policy"
      
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::stop_continuation"
      "claude_code/public_governance_surface.py::stop_continuation"
      
      [ .exactMatch "block" .deny
        ]
      .deny
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::subagent_start_review"
      "claude_code/public_governance_surface.py::subagent_start_review"
      
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::subagent_stop_review"
      "claude_code/public_governance_surface.py::subagent_stop_review"
      
      [ .exactMatch "allow" .permit
        ]
      .permit
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::user_prompt_expansion_guard"
      "claude_code/public_governance_surface.py::user_prompt_expansion_guard"
      
      [ .exactMatch "block" .deny
        ]
      .deny
      .firstMatch
    ,     .binary "claude_code/public_governance_surface.py::user_prompt_submit_guard"
      "claude_code/public_governance_surface.py::user_prompt_submit_guard"
      
      [ .exactMatch "ask" .escalate
        ]
      .escalate
      .firstMatch
    ]
  edges :=
    [ { fromNode := "claude_code/public_governance_surface.py::registration::ConfigChange::config_change_review", toNode := "claude_code/public_governance_surface.py::config_change_review", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::InstructionsLoaded::instructions_loaded_review", toNode := "claude_code/public_governance_surface.py::instructions_loaded_review", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::Notification::notification_review", toNode := "claude_code/public_governance_surface.py::notification_review", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::PermissionRequest::permission_request_decision", toNode := "claude_code/public_governance_surface.py::permission_request_decision", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::PostToolUse::post_tool_use_observation", toNode := "claude_code/public_governance_surface.py::post_tool_use_observation", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::PreCompact::pre_compact_review", toNode := "claude_code/public_governance_surface.py::pre_compact_review", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::PreToolUse::pre_tool_use_permission_decision", toNode := "claude_code/public_governance_surface.py::pre_tool_use_permission_decision", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::SessionStart::session_start_policy", toNode := "claude_code/public_governance_surface.py::session_start_policy", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::Setup::setup_policy", toNode := "claude_code/public_governance_surface.py::setup_policy", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::Stop::stop_continuation", toNode := "claude_code/public_governance_surface.py::stop_continuation", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::SubagentStart::subagent_start_review", toNode := "claude_code/public_governance_surface.py::subagent_start_review", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::SubagentStop::subagent_stop_review", toNode := "claude_code/public_governance_surface.py::subagent_stop_review", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::UserPromptExpansion::user_prompt_expansion_guard", toNode := "claude_code/public_governance_surface.py::user_prompt_expansion_guard", transform := .passThrough }
    , { fromNode := "claude_code/public_governance_surface.py::registration::UserPromptSubmit::user_prompt_submit_guard", toNode := "claude_code/public_governance_surface.py::user_prompt_submit_guard", transform := .passThrough }
    ]

/-- Claude Code public surface extracted-graph audit subject. -/
def claudeCodeHooksExtractedGraph : AuditSubject where
  graph := claudeCodeHooksExtractedGovernanceGraph
  evalNode := auditEvaluateNode

def claudeCodeHooksGovernanceAdmissibilityVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict claudeCodeHooksExtractedGraph

/-- The Claude Code public hook/settings/command surface rejects monotonicity. -/
theorem claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity :
    claudeCodeHooksGovernanceAdmissibilityVerdict =
      AuditVerdict.rejected AuditCheck.monotonicity := by
  native_decide

def claudeCodeHooksGovernanceAdmissibilityVerdictReviewRequired : AuditVerdict :=
  governanceAdmissibilityVerdictReviewRequired claudeCodeHooksExtractedGraph

/-- Review-required compatibility theorem for the Claude Code public hook lane. -/
theorem claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired :
    claudeCodeHooksGovernanceAdmissibilityVerdictReviewRequired =
      AuditVerdict.rejected AuditCheck.monotonicity := by
  native_decide

/-- Legacy hand-authored uniform-triangle spectral carrier for the Claude Code
threshold-rejection bundle, superseded by the derived projection in
`Legitimacy.CaseStudies.ClaudeCodeHarness` and retained for citation
stability. -/
def claudeCodeHarnessSpectralGraph : GovGraph ℚ 3 :=
  uniTriGraph

/-- Legacy hand-authored rank signal for the Claude Code threshold-rejection
bundle, superseded by the graph-derived failure signal in
`Legitimacy.CaseStudies.ClaudeCodeHarness` and retained for citation stability.
-/
def claudeCodeHarnessFailureSignal : Fin 3 → ℚ :=
  sig

/-- Legacy Claude Code audit tolerance for the C* threshold; retained as the
tolerance reused by the derived carrier. -/
def claudeCodeHarnessTolerance : ℚ :=
  1 / 10

/-- Exact critical capability value for the legacy hand-authored Claude Code
carrier: `1/10`. The derived projection proves the same value under
`claudeCodeHarnessDerived_C_star_value`. -/
theorem claudeCodeHarness_C_star_value :
    C_star claudeCodeHarnessSpectralGraph
      claudeCodeHarnessFailureSignal
      claudeCodeHarnessTolerance = 1 / 10 := by
  exact concrete_C_star_values.1

/-- The committed Claude Code extracted graph has the finite public governance surface used
by the v1.0.0 binary evidence bundle. -/
theorem claudeCodeHarness_extracted_node_count :
    claudeCodeHooksExtractedGovernanceGraph.nodes.length = 31 := by
  native_decide

/-- The committed Claude Code extracted graph has registration-to-handler edges
in the public-surface fixture. -/
theorem claudeCodeHarness_extracted_edge_count :
    claudeCodeHooksExtractedGovernanceGraph.edges.length = 14 := by
  native_decide

end Legitimacy
