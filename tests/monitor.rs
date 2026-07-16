use legitimacy::{
    CompiledGraph, DeclaredSacrifice, GovernanceEventSource, GovernanceMonitoringEvent,
    GovernanceProperty, MonitorSession, MonitoringSpec, SacrificeProvenance,
    StrategyproofnessVerdict, monitor,
};
use std::collections::BTreeMap;

#[test]
fn monitor_alerts_when_monotonicity_violation_exceeds_declared_bound() {
    let session = MonitorSession {
        compiled_graph: CompiledGraph {
            name: "fixture-graph".to_string(),
            version: "1.0".to_string(),
            axiom_verdicts: Vec::new(),
            strategyproofness: StrategyproofnessVerdict::Strategyproof,
            family_description: "synthetic".to_string(),
            compiled_at: "2026-04-15T00:00:00Z".to_string(),
        },
        declared_sacrifices: vec![DeclaredSacrifice {
            sacrificed_property: GovernanceProperty::Monotonicity,
            justification: "known monotonicity tradeoff".to_string(),
            impact_bound: 0.3,
            monitoring_plan: vec![MonitoringSpec {
                metric: "monotonicity.claim_strength_delta".to_string(),
                threshold: 0.3,
                frequency_seconds: 60,
                alert_channel: "governance-risk.monotonicity".to_string(),
            }],
            provenance: SacrificeProvenance {
                compiled_kind: legitimacy::CompiledGovernanceKind::Graph,
                compiled_name: "fixture-graph".to_string(),
                compiled_version: "1.0".to_string(),
                compiled_at: "2026-04-15T00:00:00Z".to_string(),
                family_description: "synthetic".to_string(),
                source_axiom: "graph monotonicity".to_string(),
                witness: "synthetic witness".to_string(),
            },
        }],
        interval_secs: 60,
        event_source: GovernanceEventSource::in_memory([GovernanceMonitoringEvent {
            property: GovernanceProperty::Monotonicity,
            actual_magnitude: 0.5,
            timestamp: "2026-04-15T00:01:00Z".to_string(),
            evidence: BTreeMap::from([("claimant".to_string(), "alice".to_string())]),
        }]),
    };

    let drift = monitor(session)
        .next()
        .expect("expected a drift event")
        .expect("monitoring should succeed");

    assert_eq!(drift.property, GovernanceProperty::Monotonicity);
    assert!((drift.declared_bound - 0.3).abs() < 1e-9);
    assert!((drift.actual_magnitude - 0.5).abs() < 1e-9);
    assert_eq!(drift.timestamp, "2026-04-15T00:01:00Z");
    assert_eq!(drift.evidence["claimant"], "alice");
}
