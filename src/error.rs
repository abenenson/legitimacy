use thiserror::Error;

#[derive(Debug, Error)]
pub enum LegitimacyError {
    #[error("strength values must be strictly positive and finite, got {value}")]
    InvalidPositiveStrength { value: f64 },

    #[error("estate totals must be strictly positive and finite, got {value}")]
    InvalidEstateTotal { value: f64 },

    #[error("claim '{claimant_id}' strength must be strictly positive and finite, got {strength}")]
    InvalidClaimStrength { claimant_id: String, strength: f64 },

    #[error("claimant ids must be non-empty, got '{claimant_id}'")]
    InvalidClaimantId { claimant_id: String },

    #[error("duplicate claimant id '{claimant_id}'")]
    DuplicateClaimantId { claimant_id: String },

    #[error("allocation is missing claimant '{claimant_id}'")]
    AllocationMissingClaimant { claimant_id: String },

    #[error("allocation for '{claimant_id}' must be non-negative and finite, got {value}")]
    InvalidAllocationValue { claimant_id: String, value: f64 },

    #[error("allocation contains unknown claimant '{claimant_id}'")]
    AllocationUnknownClaimant { claimant_id: String },

    #[error("allocation total {total_allocated} exceeds estate total {estate_total}")]
    AllocationExceedsEstate {
        total_allocated: f64,
        estate_total: f64,
    },

    #[error("allocation is missing claimant '{claimant_id}' during {context}")]
    MissingAllocationShare {
        claimant_id: String,
        context: String,
    },

    #[error("rule '{rule_name}' v{rule_version} is not admissible")]
    RuleNotAdmissible {
        rule_name: String,
        rule_version: String,
    },

    #[error(
        "compiled rule '{compiled_rule_name}' v{compiled_rule_version} does not match runtime rule '{rule_name}' v{rule_version}"
    )]
    CertificationRuleMismatch {
        compiled_rule_name: String,
        compiled_rule_version: String,
        rule_name: String,
        rule_version: String,
    },

    #[error(
        "certificate outcome mismatch for claimant '{claimant_id}' under '{rule_name}' v{rule_version}: expected {expected}, got {actual}"
    )]
    CertifiedOutcomeMismatch {
        rule_name: String,
        rule_version: String,
        claimant_id: String,
        expected: f64,
        actual: f64,
    },

    #[error("failed to read policy file '{path}': {source}")]
    PolicyRead {
        path: String,
        #[source]
        source: std::io::Error,
    },

    #[error("failed to parse policy '{context}': {source}")]
    PolicyToml {
        context: String,
        #[source]
        source: toml::de::Error,
    },

    #[error("invalid policy '{context}': {message}")]
    InvalidPolicy { context: String, message: String },

    #[error("node ids must be non-empty, got '{value}'")]
    InvalidNodeId { value: String },

    #[error("graph already contains node '{node_id}'")]
    DuplicateNodeId { node_id: String },

    #[error("graph edge references unknown node '{node_id}'")]
    InvalidEdgeReference { node_id: String },

    #[error("unsupported governance node '{node_id}' of type '{node_type}'")]
    UnsupportedNodeType { node_id: String, node_type: String },

    #[error("claim '{claimant_id}' has invalid governance strength {strength}")]
    InvalidGovernanceStrength { claimant_id: String, strength: f64 },

    #[error("gate '{gate}' is invalid: {message}")]
    InvalidGate { gate: String, message: String },

    #[error("invalid regex '{pattern}': {source}")]
    InvalidRegex {
        pattern: String,
        #[source]
        source: regex::Error,
    },

    #[error("conflicting claim feed for claimant '{claimant_id}' at node '{node_id}'")]
    ConflictingClaimFeed {
        node_id: String,
        claimant_id: String,
    },

    #[error("graph contains no entry nodes")]
    NoEntryNodes,

    #[error("cycle detected with no convergence handling: {cycle:?}")]
    CycleError { cycle: Vec<String> },

    #[error("failed to read {context}: {source}")]
    Io {
        context: String,
        #[source]
        source: std::io::Error,
    },

    #[error("failed to parse JSON for {context}: {source}")]
    Json {
        context: String,
        #[source]
        source: serde_json::Error,
    },

    #[error("failed to serialize {context}: {source}")]
    Serialize {
        context: String,
        #[source]
        source: serde_json::Error,
    },

    #[error("sqlite error while {context}: {source}")]
    Sqlite {
        context: String,
        #[source]
        source: rusqlite::Error,
    },

    #[error("system clock error: {source}")]
    SystemClock {
        #[from]
        source: std::time::SystemTimeError,
    },

    #[error("{message}")]
    InvalidInput { message: String },
}

impl LegitimacyError {
    #[tracing::instrument(skip(message))]
    pub fn invalid_input(message: impl Into<String>) -> Self {
        Self::InvalidInput {
            message: message.into(),
        }
    }

    pub(crate) fn invalid_policy(context: impl Into<String>, message: impl Into<String>) -> Self {
        Self::InvalidPolicy {
            context: context.into(),
            message: message.into(),
        }
    }

    pub(crate) fn missing_allocation_share(
        claimant_id: impl Into<String>,
        context: impl Into<String>,
    ) -> Self {
        Self::MissingAllocationShare {
            claimant_id: claimant_id.into(),
            context: context.into(),
        }
    }
}
