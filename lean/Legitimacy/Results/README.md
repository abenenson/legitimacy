# Legitimacy.Results

The `Results/` Lean directory is intentionally flat. These modules are theorem
surfaces, so moving them into subdirectories would churn public import paths
without changing the proof ownership.

Conceptual clusters:

- `Admissibility`: `GovernanceAdmissibilityAudit`,
  `AutoGenAdmissibilityAudit`, `CodexAdmissibilityAudit`,
  `ClaudeAgentSDKAdmissibilityAudit`, `CrewAIAdmissibilityAudit`,
  `OpenClawAdmissibilityAudit`, `LeaderboardAdmissibilityAudits`.
- `Bridge`: `UnbundledCorrigibilityBridge`, `SemanticBridge`,
  `BottleneckBridgeRefutation`, `N7BridgeDischarge`.
- `Foundations`: `Composition`, `DiagnosticAxiomIff`, `Impossibility`,
  `Proportional`, `NonPeerRelative`, `Refinement`.
- `Self`: `SelfMod`, `SelfModBoundary`, `SelfAudit`.
- `ASI`: `ASIGovernanceReliability`, `BasinIsASIClassification`,
  `BifurcationKernel`.
- `Other theorem surfaces`: `Amplification`, `MultiPrincipal`, `Temporal`.

New result files should either fit one of these clusters or update this map.
