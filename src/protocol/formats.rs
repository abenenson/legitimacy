use crate::{Decision, GovernanceFactorExposure, GovernanceGraph, GovernanceProperty};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use super::state::{DeclaredSacrifice, SacrificeDeclaration};

fn default_protocol_graph_name() -> String {
    "spectral-governance".to_string()
}

fn default_protocol_graph_version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct GovernanceDeclaration {
    pub protocol_version: String,
    pub timestamp: String,
    #[serde(default = "default_protocol_graph_name")]
    pub graph_name: String,
    #[serde(default = "default_protocol_graph_version")]
    pub graph_version: String,
    pub graph: GovernanceGraph,
    pub sacrifices: Vec<DeclaredSacrifice>,
    pub spectral_gap: f64,
    pub cv_bound: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct PromotionCertificate {
    pub rule_name: String,
    pub claimant_id: String,
    pub decision: Decision,
    pub outcome_verified: bool,
    #[serde(default)]
    pub evidence: BTreeMap<String, String>,
    pub compiled_rule_hash: String,
    pub prev_cert_hash: Option<String>,
    pub timestamp: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct GovernanceDriftAlert {
    pub alert_type: String,
    pub property: GovernanceProperty,
    pub declared_bound: f64,
    pub actual_magnitude: f64,
    #[serde(default)]
    pub evidence: BTreeMap<String, String>,
    pub recommended_action: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct GovernanceRiskReport {
    pub factor_exposure: GovernanceFactorExposure,
    pub spectral_gap: f64,
    pub cv_bound: f64,
    pub localizability_bound: f64,
}

pub type SerializableSacrifice = SacrificeDeclaration;
