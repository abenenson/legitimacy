//! Promotion certificates for admissible compiled rules.

use std::collections::BTreeMap;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::{
    Certificate, Claim, CompiledRule, EPSILON, Estate, LegitimacyError, Rule, evaluate_rule,
    ledger::Ledger,
};

const CERTIFICATION_CONTEXT: &str = "certificate verification";

pub struct CertificationContext<'a> {
    pub compiled_rule: &'a CompiledRule,
    pub rule: &'a Rule,
    pub claims: &'a [Claim],
    pub estate: &'a Estate,
}

/// Issue a promotion certificate for a concrete governed act.
#[tracing::instrument(
    skip(context, evidence),
    fields(
        claimant_id = claimant_id,
        admissible = context.compiled_rule.is_admissible()
    )
)]
pub fn certify(
    context: &CertificationContext<'_>,
    act_description: &str,
    claimant_id: &str,
    outcome: f64,
    evidence: BTreeMap<String, String>,
) -> Result<Certificate, LegitimacyError> {
    ensure_matching_rule(context.compiled_rule, context.rule)?;

    if !context.compiled_rule.is_admissible() {
        return Err(LegitimacyError::RuleNotAdmissible {
            rule_name: context.compiled_rule.name.clone(),
            rule_version: context.compiled_rule.version.clone(),
        });
    }

    let expected_outcome = expected_certified_outcome(context, claimant_id)?;
    ensure_matching_outcome(
        context.compiled_rule,
        claimant_id,
        expected_outcome,
        outcome,
    )?;

    let certificate = Certificate {
        rule_name: context.compiled_rule.name.clone(),
        rule_version: context.compiled_rule.version.clone(),
        compiled_rule_hash: context.compiled_rule.content_hash()?,
        act_description: act_description.to_string(),
        claimant_id: claimant_id.to_string(),
        outcome,
        evidence,
        issued_at: issued_at()?,
        admissible: true,
    };

    Ledger::open_default()?.record_certificate(&certificate)?;

    Ok(certificate)
}

fn expected_certified_outcome(
    context: &CertificationContext<'_>,
    claimant_id: &str,
) -> Result<f64, LegitimacyError> {
    evaluate_rule(
        context.rule,
        context.claims,
        context.estate,
        CERTIFICATION_CONTEXT,
    )?
    .share_for(claimant_id, CERTIFICATION_CONTEXT)
}

fn ensure_matching_rule(compiled_rule: &CompiledRule, rule: &Rule) -> Result<(), LegitimacyError> {
    if compiled_rule.name == rule.name && compiled_rule.version == rule.version {
        return Ok(());
    }

    Err(LegitimacyError::CertificationRuleMismatch {
        compiled_rule_name: compiled_rule.name.clone(),
        compiled_rule_version: compiled_rule.version.clone(),
        rule_name: rule.name.clone(),
        rule_version: rule.version.clone(),
    })
}

fn ensure_matching_outcome(
    compiled_rule: &CompiledRule,
    claimant_id: &str,
    expected_outcome: f64,
    actual_outcome: f64,
) -> Result<(), LegitimacyError> {
    let tolerance = EPSILON + EPSILON * (expected_outcome.abs() + actual_outcome.abs());
    if (expected_outcome - actual_outcome).abs() <= tolerance {
        return Ok(());
    }

    Err(LegitimacyError::CertifiedOutcomeMismatch {
        rule_name: compiled_rule.name.clone(),
        rule_version: compiled_rule.version.clone(),
        claimant_id: claimant_id.to_string(),
        expected: expected_outcome,
        actual: actual_outcome,
    })
}

fn issued_at() -> Result<String, LegitimacyError> {
    let seconds = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs() as i64;
    let days = seconds.div_euclid(86_400);
    let seconds_of_day = seconds.rem_euclid(86_400);
    let (year, month, day) = civil_from_days(days);
    let hour = seconds_of_day / 3_600;
    let minute = (seconds_of_day % 3_600) / 60;
    let second = seconds_of_day % 60;

    Ok(format!(
        "{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z"
    ))
}

fn civil_from_days(days_since_unix_epoch: i64) -> (i32, u32, u32) {
    let shifted_days = days_since_unix_epoch + 719_468;
    let era = if shifted_days >= 0 {
        shifted_days
    } else {
        shifted_days - 146_096
    } / 146_097;
    let day_of_era = shifted_days - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let year = year_of_era + era * 400;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_piece = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_piece + 2) / 5 + 1;
    let month = month_piece + if month_piece < 10 { 3 } else { -9 };
    let year = year + if month <= 2 { 1 } else { 0 };

    (year as i32, month as u32, day as u32)
}
