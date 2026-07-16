/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Legitimacy.Reflective.Depth2

/-!
# Reflective worked-example consumers

This module keeps downstream uses separate from the substrate definitions. The
depth-2 example is intentionally modal-axiomatic: audit-to-box uses
godel-loeb's `loeb`, while box-to-audit is the encoded round-trip direction
whose Knaster-Tarski fixed-state alignment is structural and whose concrete
forcing witness factors through an audit certificate.

The kernel-safety `SelfAudit` reflective composition remains outside the
current substrate. The current threshold-pipeline encoding does not yet expose
a non-trivial reflective fixed point on the legitimacy graph itself.
-/

namespace Legitimacy
namespace Reflective
namespace ReflectiveGovernanceFixedPointSystem

/--
External consumer for the non-`Set.univ` depth-2 worked example.

The theorem consumes the Löb-discharged audit certificate and then uses the
Knaster-Tarski fixed-point agreement theorem to transfer it into the agent's
self-model. This closes the previous "no external consumers" gap for the
worked example family.
-/
theorem depth2ReflectiveSystem_selfModel_certified_from_loeb
    (hinternal :
      reflectiveBox (stableAuditSoundFormula depth2ReflectiveSystem)) :
    (depth2ReflectiveSystem.selfModel depth2ReflectiveSystem.stable).auditVerdict := by
  exact (stable_selfModel_iff_audit depth2ReflectiveSystem).2
    (depth2ReflectiveSystem_loeb_audit_certified hinternal)

end ReflectiveGovernanceFixedPointSystem
end Reflective
end Legitimacy
