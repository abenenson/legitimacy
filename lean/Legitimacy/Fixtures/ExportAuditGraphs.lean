/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/
import Lean
import Legitimacy.Results.CodexAdmissibilityAudit
import Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit
import Legitimacy.Results.ClaudeCodeAdmissibilityAudit

/-!
Evaluate the actual graph constants cited by the audit CLI. This executable
exports every node field, gate (in evaluation order), and edge. The checker
compares these values to the Rust JSON fixtures; searching Lean source text
cannot detect changed defaults, gate order, duplicate nodes, or dead literals.
Numeric values use exact rational strings so the comparison never rounds them.
This is a value-parity gate, not a proof of the Rust compiler or extractor.
-/
set_option autoImplicit false
open Lean Legitimacy

namespace AuditGraphExport

private def text := Json.str
private def array (xs : List Json) : Json := Json.arr xs.toArray
private def obj := Json.mkObj
private def rational (q : ℚ) : Json := text (toString q.num ++ "/" ++ toString q.den)

private def decision : AuditDecision → Json
  | .permit => text "Permit"
  | .deny => text "Deny"
  | .escalate => text "Escalate"

private def combination : AuditGateLogic → Json
  | .allMustPass => text "AllMustPass"
  | .anyMustPass => text "AnyMustPass"
  | .firstMatch => text "FirstMatch"

private def gate : AuditGate → Json
  | .prefixMatch p d => obj [("PrefixMatch", obj [("pattern", text p), ("decision", decision d)])]
  | .exactMatch v d => obj [("ExactMatch", obj [("value", text v), ("decision", decision d)])]
  | .contentMatch r d => obj [("ContentMatch", obj [("regex", text r), ("decision", decision d)])]
  | .thresholdGate f m d => obj [("ThresholdGate", obj [("field", text f), ("min", rational m),
      ("decision", decision d)])]
  | .peerRelative f p d => obj [("PeerRelative", obj [("field", text f), ("percentile", rational p),
      ("decision", decision d)])]

private def node : AuditGovernanceNode → Json
  | .binary i n gs d c => obj [("Binary", obj [("id", text i), ("name", text n),
      ("gates", array (gs.map gate)), ("default", decision d), ("combination", combination c)])]
  | .proportional i n r ps => obj [("Proportional", obj [("id", text i), ("name", text n),
      ("rule", text r), ("priority_classes", array (ps.map text))])]
  | .threshold i n t f => obj [("Threshold", obj [("id", text i), ("name", text n),
      ("threshold", rational t), ("field", text f)])]

private def transform : AuditEdgeTransform → Json
  | .passThrough => text "PassThrough"
  | .claimModification d => obj [("ClaimModification", obj [("delta", rational d)])]

private def edge (e : AuditGovernanceEdge) : Json :=
  obj [("from", text e.fromNode), ("to", text e.toNode), ("transform", transform e.transform)]

private def graph (g : AuditGovernanceGraph) : Json :=
  obj [("nodes", array (g.nodes.map node)), ("edges", array (g.edges.map edge))]

-- Keep nodes as a list here: constructing a JSON object would hide duplicate IDs.
def exportGraphs : Json := obj [
  ("codex-cli", graph codexHooksExtractedGovernanceGraph),
  ("claude-agent-sdk", graph claudeAgentSDKHooksExtractedGovernanceGraph),
  ("claude-code", graph claudeCodeHooksExtractedGovernanceGraph)]

end AuditGraphExport

def main : IO Unit := IO.println AuditGraphExport.exportGraphs.compress
