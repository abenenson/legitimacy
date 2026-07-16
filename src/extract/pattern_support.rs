use crate::extract::ParsedFunction;
use crate::{Decision, Gate};

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct SignalSummary {
    pub(crate) positive: usize,
    pub(crate) negative: usize,
    pub(crate) contextual: usize,
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct BranchSummary {
    pub(crate) total: usize,
    pub(crate) positive: usize,
    pub(crate) negative: usize,
    pub(crate) contextual: usize,
}

pub(crate) fn gate_decision(gate: &Gate) -> &Decision {
    match gate {
        Gate::PrefixMatch { decision, .. }
        | Gate::ExactMatch { decision, .. }
        | Gate::ContentMatch { decision, .. }
        | Gate::ThresholdGate { decision, .. }
        | Gate::PeerRelative { decision, .. } => decision,
    }
}

pub(crate) fn signal_summary(text: &str) -> SignalSummary {
    let lower = text.to_ascii_lowercase();
    let mut summary = SignalSummary::default();

    if contains_any_phrase(
        &lower,
        &[
            "should_block: false",
            "should_block = false",
            "should_stop: false",
            "should_stop = false",
            "return true",
            "=> true",
            "blocked: false",
            "blocked = false",
            "deny: false",
            "deny = false",
            "rejected: false",
            "rejected = false",
            "allowed: true",
            "allowed = true",
            "allowlisted: true",
            "allowlisted = true",
            "approved: true",
            "approved = true",
            "permit: true",
            "permit = true",
            "\"behavior\": \"allow\"",
            "behavior: \"allow\"",
            "literal[\"allow\"]",
        ],
    ) {
        summary.positive += 1;
    }

    if contains_any_phrase(
        &lower,
        &[
            "should_block: true",
            "should_block = true",
            "should_stop: true",
            "should_stop = true",
            "return false",
            "=> false",
            "blocked: true",
            "blocked = true",
            "allowed: false",
            "allowed = false",
            "allowlisted: false",
            "allowlisted = false",
            "approved: false",
            "approved = false",
            "permit: false",
            "permit = false",
            "\"behavior\": \"deny\"",
            "behavior: \"deny\"",
            "literal[\"deny\"]",
            "literal[\"block\"]",
        ],
    ) {
        summary.negative += 1;
    }

    if has_any_token_prefix(&lower, &["permit", "approv", "allow", "allowlist"]) {
        summary.positive += 1;
    }

    if has_any_token_prefix(&lower, &["deny", "block", "reject", "forbid", "disallow"]) {
        summary.negative += 1;
    }

    if has_any_token_prefix(
        &lower,
        &[
            "approval",
            "permission",
            "guard",
            "review",
            "hook",
            "sandbox",
            "policy",
            "allowlist",
        ],
    ) {
        summary.contextual += 1;
    }

    summary
}

pub(crate) fn decision_for_text(text: &str) -> Option<Decision> {
    let signals = signal_summary(text);
    if signals.positive > 0 && signals.negative == 0 {
        return Some(Decision::Permit);
    }
    if signals.negative > 0 && signals.positive == 0 {
        return Some(Decision::Deny);
    }
    if signals.positive > 0 && signals.negative > 0 {
        return Some(Decision::Escalate);
    }

    let lower = text.to_ascii_lowercase();
    if has_any_token_prefix(
        &lower,
        &[
            "permission",
            "approval",
            "review",
            "guard",
            "confirm",
            "escalat",
            "sandbox",
            "policy",
            "hook",
            "callback",
            "tool_call",
            "event",
            "handler",
            "restricted",
            "defer",
        ],
    ) {
        return Some(Decision::Escalate);
    }

    None
}

pub(crate) fn has_governance_keyword(text: &str) -> bool {
    has_any_token_prefix(
        &text.to_ascii_lowercase(),
        &[
            "approv",
            "permit",
            "deny",
            "block",
            "allow",
            "allowlist",
            "permission",
            "guard",
            "review",
            "sandbox",
            "hook",
            "policy",
            "invalid",
            "unsupported",
            "reject",
        ],
    )
}

pub(crate) fn contains_any_phrase(text: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| text.contains(needle))
}

pub(crate) fn has_any_token_prefix(text: &str, prefixes: &[&str]) -> bool {
    tokenize(text)
        .into_iter()
        .any(|token| prefixes.iter().any(|prefix| token.starts_with(prefix)))
}

pub(crate) fn tokenize(text: &str) -> Vec<String> {
    text.split(|character: char| !character.is_ascii_alphanumeric() && character != '_')
        .filter(|token| !token.is_empty())
        .map(|token| token.to_ascii_lowercase())
        .collect()
}

pub(crate) fn should_promote_literal(parsed: &ParsedFunction, literal: &str) -> bool {
    !literal.trim().is_empty()
        && (has_governance_keyword(literal)
            || looks_like_policy_target(literal)
            || (mentions_hook_registration(parsed) && has_hook_keyword(literal))
            || ((parsed.has_if_chain || !parsed.match_arms.is_empty())
                && (has_policy_target_keyword(&parsed.body_text)
                    || parsed
                        .condition_texts
                        .iter()
                        .any(|condition| has_policy_target_keyword(condition)))))
}

fn looks_like_policy_target(literal: &str) -> bool {
    let trimmed = literal.trim();
    if trimmed.is_empty() {
        return false;
    }

    trimmed.starts_with('/')
        || trimmed.contains(std::path::MAIN_SEPARATOR)
        || trimmed.contains(".rs")
        || trimmed.contains(".ts")
        || trimmed.contains(".tsx")
        || trimmed.contains(".toml")
        || trimmed.contains(".json")
        || trimmed.contains(' ')
        || trimmed.contains('\t')
        || trimmed.contains("::")
        || trimmed.contains("&&")
        || trimmed.contains("||")
        || trimmed.contains(';')
        || trimmed.chars().all(|character| {
            character.is_ascii_alphanumeric() || matches!(character, '_' | '-' | ':' | '.')
        })
}

pub(crate) fn has_policy_target_keyword(text: &str) -> bool {
    has_any_token_prefix(
        &text.to_ascii_lowercase(),
        &["tool", "command", "path", "argv", "exec", "bash", "shell"],
    )
}

fn has_hook_keyword(text: &str) -> bool {
    has_any_token_prefix(
        &text.to_ascii_lowercase(),
        &[
            "hook",
            "callback",
            "handler",
            "event",
            "tool_call",
            "session_start",
            "before_agent_start",
        ],
    )
}

pub(crate) fn mentions_hook_registration(parsed: &ParsedFunction) -> bool {
    parsed
        .calls
        .iter()
        .any(|call| is_hook_registration_call(call))
        || parsed
            .callback_refs
            .iter()
            .any(|callback| has_hook_keyword(callback))
        || parsed
            .string_literals
            .iter()
            .any(|literal| has_hook_keyword(literal))
        || has_any_token_prefix(&parsed.body_text, &["callback"])
        || contains_any_phrase(&parsed.body_text, &["hook_run", "hook_completed"])
}

fn is_hook_registration_call(call: &str) -> bool {
    matches!(
        call,
        "select_handlers"
            | "execute_handlers"
            | "register_handler"
            | "registertool"
            | "registercommand"
            | "registerflag"
            | "registershortcut"
            | "registerunhandledrejectionhandler"
    ) || has_any_token_prefix(&call.to_ascii_lowercase(), &["register", "handler", "hook"])
}

#[cfg(test)]
mod tests {
    use super::{decision_for_text, has_governance_keyword, signal_summary};
    use crate::Decision;

    #[test]
    fn disallow_counts_as_negative_without_false_positive_allow_signal() {
        let signals = signal_summary("if disallow_delete(action) { return blocked; }");
        assert_eq!(signals.positive, 0);
        assert!(signals.negative > 0);
        assert_eq!(
            decision_for_text("if disallow_delete(action) { return blocked; }"),
            Some(Decision::Deny)
        );
    }

    #[test]
    fn allowlisted_still_counts_as_positive_governance_signal() {
        let signals = signal_summary("allowlisted = true");
        assert!(signals.positive > 0);
        assert!(has_governance_keyword("allowlisted tool"));
    }
}
