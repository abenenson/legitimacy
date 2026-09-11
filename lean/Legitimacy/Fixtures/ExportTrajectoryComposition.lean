/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.TrajectoryCompositionGenerated.Fixtures

/-! Lean-computed JSON projection consumed by Rust trajectory composition parity tests. -/

set_option autoImplicit false

namespace Legitimacy.Fixtures

private def quote (value : String) : String := "\"" ++ value ++ "\""

private def eventJson (index : Nat) (event : NormalizedEventOccurrenceV0) : String :=
  "{" ++
    "\"occurrence_index\":" ++ toString index ++ "," ++
    "\"claimant_wire_id\":" ++ quote ("occurrence:" ++ toString index) ++ "," ++
    "\"strength_numerator\":" ++ toString (index + 1) ++ "," ++
    "\"strength_denominator\":1," ++
    "\"event_id\":" ++ quote event.eventId ++ "," ++
    "\"kind\":" ++ quote event.kind.label ++ "," ++
    "\"source_item_id\":" ++ quote (event.sourceItemId.getD "") ++ "," ++
    "\"raw_record_digest\":" ++ quote event.rawRecordDigest ++ "," ++
    "\"canonical_event_digest\":" ++ quote event.canonicalEventDigest ++
  "}"

private def eventsJson (events : List NormalizedEventOccurrenceV0) : String :=
  "[" ++ String.intercalate "," (events.mapIdx eventJson) ++ "]"

private def badPrefixJson : Option BadPrefixPosition → String
  | none => "null"
  | some position =>
      "{" ++
        "\"transition_index\":" ++ toString position.transitionIndex ++ "," ++
        "\"prefix_length\":" ++ toString position.prefixLength ++ "," ++
        "\"denied_occurrence_index\":" ++ toString position.deniedOccurrenceIndex ++
      "}"

private def fixtureJson
    (name trajectoryDigest replayFinalHead traceFileSha256 : String)
    (events : List NormalizedEventOccurrenceV0) : String :=
  "{" ++
    "\"name\":" ++ quote name ++ "," ++
    "\"trajectory_digest\":" ++ quote trajectoryDigest ++ "," ++
    "\"replay_final_head\":" ++ quote replayFinalHead ++ "," ++
    "\"trace_file_sha256\":" ++ quote traceFileSha256 ++ "," ++
    "\"events\":" ++ eventsJson events ++ "," ++
    "\"all_singletons_permit\":" ++
      toString (allSingletonsPermitBool generatedTrajectoryCompiledGovernanceV0 events) ++ "," ++
    "\"first_bad_prefix\":" ++
      badPrefixJson (firstBadPrefix? generatedTrajectoryCompiledGovernanceV0 events) ++
  "}"

def trajectoryCompositionParityJson : String :=
  "{" ++
    "\"policy_identity\":" ++ quote generatedTrajectoryPolicyIdentityV0 ++ "," ++
    "\"policy_version\":" ++ quote generatedTrajectoryPolicyVersionV0 ++ "," ++
    "\"policy_artifact_digest\":" ++
      quote generatedTrajectoryPolicyArtifactDigestV0 ++ "," ++
    "\"policy_source_sha256\":" ++
      quote generatedTrajectoryPolicySourceSha256V0 ++ "," ++
    "\"occurrence_encoder_identity\":" ++
      quote generatedTrajectoryOccurrenceEncoderIdentityV0 ++ "," ++
    "\"occurrence_encoder_version\":" ++
      quote generatedTrajectoryOccurrenceEncoderVersionV0 ++ "," ++
    "\"historical_property_identity\":" ++
      quote generatedTrajectoryHistoricalPropertyIdentityV0 ++ "," ++
    "\"historical_property_version\":" ++
      quote generatedTrajectoryHistoricalPropertyVersionV0 ++ "," ++
    "\"fixtures\":[" ++
      fixtureJson "benign" benignTrajectoryDigestV0 benignReplayFinalHeadV0
        benignTraceFileSha256V0
        benignTrajectoryEventsV0 ++ "," ++
      fixtureJson "red" redTrajectoryDigestV0 redReplayFinalHeadV0 redTraceFileSha256V0
        redTrajectoryEventsV0 ++
    "]}"

end Legitimacy.Fixtures

def main : IO Unit :=
  IO.println Legitimacy.Fixtures.trajectoryCompositionParityJson
