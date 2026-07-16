use clap::ValueEnum;
use legitimacy::{
    ClaimCorpusProvenance, ExtractionReviewOverlay, GovernanceClaim, GovernanceGraph,
    LegitimacyError, ObservedRuntimeClaimRecord, load_observed_runtime_corpus_pack,
    validate_governance_graph,
};
use std::{fs, path::Path};

pub(crate) fn load_claim_corpus(path: &Path) -> Result<Vec<GovernanceClaim>, LegitimacyError> {
    if path.is_dir() {
        return Ok(load_observed_runtime_corpus_pack(path)?.governance_claims());
    }

    let input = fs::read_to_string(path).map_err(|source| LegitimacyError::Io {
        context: format!("reading claim corpus '{}'", path.display()),
        source,
    })?;

    if input.trim().is_empty() {
        return Err(LegitimacyError::invalid_input(format!(
            "claim corpus '{}' is empty",
            path.display()
        )));
    }

    let trimmed = input.trim_start();
    if trimmed.starts_with('[') {
        return serde_json::from_str::<Vec<GovernanceClaim>>(&input).map_err(|source| {
            LegitimacyError::Json {
                context: format!("claim corpus '{}'", path.display()),
                source,
            }
        });
    }

    let mut claims = Vec::new();
    for (index, line) in input.lines().enumerate() {
        let line_number = index + 1;
        if line.trim().is_empty() {
            continue;
        }
        let claim = match serde_json::from_str::<GovernanceClaim>(line) {
            Ok(claim) => claim,
            Err(_) => serde_json::from_str::<ObservedRuntimeClaimRecord>(line)
                .map(|record| record.claim)
                .map_err(|source| LegitimacyError::Json {
                    context: format!("claim corpus '{}' line {line_number}", path.display()),
                    source,
                })?,
        };
        claims.push(claim);
    }

    if claims.is_empty() {
        return Err(LegitimacyError::invalid_input(format!(
            "claim corpus '{}' did not contain any claims",
            path.display()
        )));
    }

    Ok(claims)
}

pub(crate) fn load_governance_graph(path: &Path) -> Result<GovernanceGraph, LegitimacyError> {
    let input = fs::read_to_string(path).map_err(|source| LegitimacyError::Io {
        context: format!("reading governance graph '{}'", path.display()),
        source,
    })?;
    let graph = serde_json::from_str(&input).map_err(|source| LegitimacyError::Json {
        context: format!("governance graph '{}'", path.display()),
        source,
    })?;
    validate_governance_graph(&graph)?;
    Ok(graph)
}

pub(crate) fn load_review_overlay(path: &Path) -> Result<ExtractionReviewOverlay, LegitimacyError> {
    let input = fs::read_to_string(path).map_err(|source| LegitimacyError::Io {
        context: format!("reading review overlay '{}'", path.display()),
        source,
    })?;
    serde_json::from_str(&input).map_err(|source| LegitimacyError::Json {
        context: format!("review overlay '{}'", path.display()),
        source,
    })
}

#[derive(Clone, Debug, ValueEnum)]
pub(crate) enum ClaimCorpusInputProvenance {
    UserSupplied,
    Fixture,
    ObservedRuntime,
    ReviewedReconstruction,
}

impl From<ClaimCorpusInputProvenance> for ClaimCorpusProvenance {
    fn from(value: ClaimCorpusInputProvenance) -> Self {
        match value {
            ClaimCorpusInputProvenance::UserSupplied => ClaimCorpusProvenance::UserSupplied,
            ClaimCorpusInputProvenance::Fixture => ClaimCorpusProvenance::Fixture,
            ClaimCorpusInputProvenance::ObservedRuntime => ClaimCorpusProvenance::ObservedRuntime,
            ClaimCorpusInputProvenance::ReviewedReconstruction => {
                ClaimCorpusProvenance::ReviewedReconstruction
            }
        }
    }
}
