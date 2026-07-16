use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum ExtractionEvidenceTier {
    Automatic,
    Reviewed,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct ExtractionReviewOverlay {
    #[serde(default)]
    pub reviewed_nodes: Vec<ReviewedNodeOverlay>,
    #[serde(default)]
    pub reviewed_edges: Vec<ReviewedEdgeOverlay>,
    #[serde(default)]
    pub alias_hints: Vec<AliasHintOverlay>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ReviewedNodeOverlay {
    pub node_id: String,
    pub note: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ReviewedEdgeOverlay {
    pub from: String,
    pub to: String,
    #[serde(default)]
    pub target_symbol: Option<String>,
    pub note: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct AliasHintOverlay {
    pub caller: String,
    pub target_symbol: String,
    pub callee: String,
    pub note: String,
}
