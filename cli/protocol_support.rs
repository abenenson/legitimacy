use legitimacy::{LegitimacyError, ProtocolLedger, ProtocolState};
use sha2::{Digest, Sha256};

pub(crate) fn protocol_error_to_verdict(error: legitimacy::ProtocolError) -> LegitimacyError {
    LegitimacyError::invalid_input(error.to_string())
}

pub(crate) fn protocol_ledger_view(
    state: &ProtocolState,
) -> Result<(ProtocolLedger, Option<legitimacy::GovernanceDriftAlert>), LegitimacyError> {
    match state {
        ProtocolState::Live { ledger, .. } => {
            Ok((ledger.clone(), ledger.drift_alerts.last().cloned()))
        }
        ProtocolState::Drifted {
            ledger,
            drift_report,
            ..
        } => Ok((ledger.clone(), Some(drift_report.clone()))),
        ProtocolState::Supervised { ledger, .. } => {
            Ok((ledger.clone(), ledger.drift_alerts.last().cloned()))
        }
        other => Err(LegitimacyError::invalid_input(format!(
            "protocol audit requires a live, supervised, or drifted state, found {}",
            other.name()
        ))),
    }
}

pub(crate) fn verify_protocol_ledger(ledger: &ProtocolLedger) -> Result<bool, LegitimacyError> {
    let mut prev_hash = None;
    for certificate in &ledger.certificates {
        if certificate.prev_cert_hash != prev_hash {
            return Ok(false);
        }
        prev_hash = Some(protocol_certificate_hash(certificate)?);
    }

    Ok(ledger.head_hash == prev_hash)
}

fn protocol_certificate_hash(
    certificate: &legitimacy::PromotionCertificate,
) -> Result<String, LegitimacyError> {
    let payload = serde_json::to_vec(certificate).map_err(|source| LegitimacyError::Serialize {
        context: "protocol certificate hash".to_string(),
        source,
    })?;
    Ok(format!("{:x}", Sha256::digest(payload)))
}
