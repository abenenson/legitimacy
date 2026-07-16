/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.TypeScriptApprovalCore.Soundness

/-!
# OpenClaw TypeScriptApprovalCore fixture

Modeled Lean fixture for the OpenClaw failover policy shape exercised by the
Rust TypeScriptApprovalCore parser/graph tests.
-/

set_option autoImplicit false

namespace Legitimacy
namespace TypeScriptApprovalCore
namespace Fixtures
namespace OpenClawFailover

def failoverReasonPolicy : PolicyDecl :=
  { name := "OpenClawFailoverReasons"
    kind := .allowlist
    entries := ["rate_limit", "overloaded", "billing", "unknown", "timeout"] }

def allowCooldownProbe : HandlerDecl :=
  { name := "shouldAllowCooldownProbeForReason"
    isAsync := false
    body :=
      .ifThenElse (.fieldEq "reason" "rate_limit")
        (.returnApproval .allow)
        (.returnApproval .deny)
    fallbackHandlers := [] }

def useTransientCooldownProbeSlot : HandlerDecl :=
  { name := "shouldUseTransientCooldownProbeSlot"
    isAsync := false
    body :=
      .ifThenElse (.fieldEq "reason" "overloaded")
        (.returnApproval .allow)
        (.returnApproval .deny)
    fallbackHandlers := [] }

def preserveTransientCooldownProbeSlot : HandlerDecl :=
  { name := "shouldPreserveTransientCooldownProbeSlot"
    isAsync := false
    body :=
      .ifThenElse (.fieldEq "reason" "model_not_found")
        (.returnApproval .allow)
        (.returnApproval .deny)
    fallbackHandlers := [] }

def program : Program :=
  .mk
    []
    []
    [failoverReasonPolicy]
    [allowCooldownProbe, useTransientCooldownProbeSlot, preserveTransientCooldownProbeSlot]
    [ { surface := "openclaw.failover.cooldownProbe"
        handler := "shouldAllowCooldownProbeForReason"
        viaDecorator := false }
    , { surface := "openclaw.failover.transientProbeSlot"
        handler := "shouldUseTransientCooldownProbeSlot"
        viaDecorator := false }
    , { surface := "openclaw.failover.preserveTransientProbeSlot"
        handler := "shouldPreserveTransientCooldownProbeSlot"
        viaDecorator := false } ]

def rateLimitClaim : ClaimQ :=
  ⟨0, 1, by norm_num, [("reason", "rate_limit")]⟩

def overloadedClaim : ClaimQ :=
  ⟨0, 1, by norm_num, [("reason", "overloaded")]⟩

def modelNotFoundClaim : ClaimQ :=
  ⟨0, 1, by norm_num, [("reason", "model_not_found")]⟩

theorem allowCooldownProbe_rate_limit_metadata_fires :
    evalRegistration program
      { surface := "openclaw.failover.cooldownProbe"
        handler := "shouldAllowCooldownProbeForReason"
        viaDecorator := false }
      [rateLimitClaim] 0 = BinaryDecision.Permit := by
  native_decide

theorem transientProbeSlot_overloaded_metadata_fires :
    evalRegistration program
      { surface := "openclaw.failover.transientProbeSlot"
        handler := "shouldUseTransientCooldownProbeSlot"
        viaDecorator := false }
      [overloadedClaim] 0 = BinaryDecision.Permit := by
  native_decide

theorem preserveProbeSlot_model_not_found_metadata_fires :
    evalRegistration program
      { surface := "openclaw.failover.preserveTransientProbeSlot"
        handler := "shouldPreserveTransientCooldownProbeSlot"
        viaDecorator := false }
      [modelNotFoundClaim] 0 = BinaryDecision.Permit := by
  native_decide

lemma extracts :
    ∃ graph : GovernanceGraph, extractTypeScriptApprovalCore program = .ok graph := by
  refine ⟨[handlerNode allowCooldownProbe,
    handlerNode useTransientCooldownProbeSlot,
    handlerNode preserveTransientCooldownProbeSlot], ?_⟩
  rfl

lemma decision_equivalent
    (graph : GovernanceGraph)
    (h : extractTypeScriptApprovalCore program = .ok graph) :
    DecisionSystem.Equivalent (sourceGovernanceGraphSemantics program) graph :=
  extractTypeScriptApprovalCore_decision_equivalent program graph h

lemma failure_reflects_source_failure
    {property : StructuralProperty}
    (graph : GovernanceGraph)
    (hextract : extractTypeScriptApprovalCore program = .ok graph)
    (hfail : ExtractedGraphFailure program.registrations graph property) :
    SourceSemanticsFailure program property :=
  typescript_approval_modeled_program_extractor_failure_reflects_modeled_source_failure
    program graph hextract hfail

end OpenClawFailover
end Fixtures
end TypeScriptApprovalCore
end Legitimacy
