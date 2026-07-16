use crate::{LegitimacyError, NodeId};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum EdgeTransform {
    PassThrough,
    ClaimModification { delta: f64 },
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct GovernanceEdge {
    pub from: NodeId,
    pub to: NodeId,
    pub transform: EdgeTransform,
}

impl GovernanceEdge {
    pub fn new(
        from: NodeId,
        to: NodeId,
        transform: EdgeTransform,
    ) -> Result<Self, LegitimacyError> {
        if let EdgeTransform::ClaimModification { delta } = transform {
            if !delta.is_finite() {
                return Err(LegitimacyError::invalid_input(format!(
                    "claim-modification delta must be finite, got {delta}"
                )));
            }
            return Ok(Self {
                from,
                to,
                transform: EdgeTransform::ClaimModification { delta },
            });
        }

        Ok(Self {
            from,
            to,
            transform,
        })
    }
}
