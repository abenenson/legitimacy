//! Finite instrumented experiment. Lean owns the transition table and proofs.
//! Rust checks boundary evidence and independently reconstructs concrete effects.
//! This is not a model-prose extractor or a production reference monitor.
mod transport;
pub use transport::{SignedRun, check_signed, parse_bundle, record_suite};

use serde::{Deserialize, Serialize};
use std::sync::OnceLock;

pub const POLICY: &str = include_str!("../../fixtures/executed-composition-v1/policy.json");
pub const TABLE: &str = include_str!("../../fixtures/executed-composition-v1/generated/table.json");
pub const PROPERTY: &str = "Legitimacy.boolJointForbiddenList";
pub const MAX_BYTES: u64 = 1024 * 1024;
const FRAGMENTS: [&str; 2] = ["SYNTHETIC-ALPHA", "SYNTHETIC-BETA"];

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum Channel {
    Public,
    Vault,
}
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum Payload {
    Fragment,
    Summary,
}
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum Decision {
    Permit,
    Deny,
    Review,
}
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum Knowledge {
    Safe,
    Violated,
    Inconclusive,
    Invalid,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Grant {
    pub principal: String,
    pub channel: Channel,
    pub payload: Payload,
    pub task: String,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Event {
    pub index: usize,
    pub principal: Option<String>,
    pub channel: Option<Channel>,
    pub payload: Option<Payload>,
    /// Supplied host session authentication, distinct from signed capture provenance.
    pub authenticated: Option<bool>,
    pub local: Decision,
    pub decision: Decision,
    /// Actual bytes delivered by the host boundary; empty means no delivery.
    pub effect: Option<String>,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Run {
    pub format: String,
    pub id: String,
    pub policy: String,
    pub guarded: bool,
    pub complete: bool,
    pub principals: Option<[String; 2]>,
    pub grants: Option<Vec<Grant>>,
    pub events: Vec<Event>,
    /// Sink readback, independent of per-event annotation.
    pub public_sink: Option<Vec<String>>,
    pub vault_sink: Option<Vec<String>>,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Report {
    pub id: String,
    pub property: String,
    pub capture_authenticated: bool,
    pub knowledge: Knowledge,
    pub governance: Decision,
    pub per_call_baseline: Decision,
    pub full_context_baseline: Decision,
    pub first_forbidden_event: Option<usize>,
    pub participating_events: Vec<usize>,
    pub exposure: Option<[bool; 2]>,
    pub reason: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Table {
    format: String,
    property: String,
    rows: Vec<[usize; 5]>,
}

/// Index encodes all 7 Boolean inputs, with no identifiers or event count.
pub fn transition(
    state: usize,
    actor: usize,
    payload: Payload,
    channel: Channel,
    authenticated: bool,
    delegated: bool,
) -> [usize; 5] {
    static ROWS: OnceLock<Vec<[usize; 5]>> = OnceLock::new();
    let rows = ROWS.get_or_init(|| {
        let t: Table = serde_json::from_str(TABLE).expect("generated Lean table JSON");
        assert_eq!(t.format, "legitimacy.executed-composition.table.v1");
        assert_eq!(t.property, PROPERTY);
        assert_eq!(t.rows.len(), 128);
        for (i, r) in t.rows.iter().enumerate() {
            assert_eq!(r[0], i);
        }
        t.rows
    });
    assert!(state < 4 && actor < 2);
    let i = state * 32
        + actor * 16
        + usize::from(payload == Payload::Fragment) * 8
        + usize::from(channel == Channel::Public) * 4
        + usize::from(authenticated) * 2
        + usize::from(delegated);
    rows[i]
}
fn decision(value: usize) -> Decision {
    if value == 1 {
        Decision::Permit
    } else {
        Decision::Deny
    }
}
fn content(actor: usize, payload: Payload) -> String {
    match payload {
        Payload::Fragment => FRAGMENTS[actor].into(),
        Payload::Summary => "SUMMARY: one synthetic fragment processed".into(),
    }
}
fn delegated(grants: &[Grant], principal: &str, channel: Channel, payload: Payload) -> bool {
    grants.iter().any(|g| {
        g.principal == principal
            && g.channel == channel
            && g.payload == payload
            && g.task == "synthetic-release"
    })
}
fn report(run: &Run, knowledge: Knowledge, reason: &str) -> Report {
    Report {
        id: run.id.clone(),
        property: PROPERTY.into(),
        capture_authenticated: false,
        knowledge,
        governance: Decision::Review,
        per_call_baseline: Decision::Review,
        full_context_baseline: Decision::Review,
        first_forbidden_event: None,
        participating_events: vec![],
        exposure: None,
        reason: reason.into(),
    }
}

/// Independent reader checker. Results come from effects plus Lean table,
/// never a supplied verdict. Missing facts remain distinct from known denials.
pub fn check(run: &Run) -> Report {
    if run.format != "legitimacy.executed-composition.run.v1" || run.policy != POLICY {
        return report(
            run,
            Knowledge::Invalid,
            "unsupported format or substituted policy/property",
        );
    }
    if run.events.len() > 256 || run.id.len() > 512 {
        return report(run, Knowledge::Invalid, "bounded experiment exceeded");
    }
    let (Some(principals), Some(grants), Some(public_sink), Some(vault_sink)) = (
        &run.principals,
        &run.grants,
        &run.public_sink,
        &run.vault_sink,
    ) else {
        return report(
            run,
            Knowledge::Inconclusive,
            "missing identity, scoped authority, or sink evidence",
        );
    };
    if !run.complete || run.events.is_empty() {
        return report(
            run,
            Knowledge::Inconclusive,
            "host completion or events unavailable",
        );
    }
    if principals[0].is_empty()
        || principals[1].is_empty()
        || principals[0] == principals[1]
        || grants.len() > 32
        || grants.iter().any(|g| !principals.contains(&g.principal))
    {
        return report(
            run,
            Knowledge::Invalid,
            "invalid declared principal set or grants",
        );
    }
    // Require complete load-bearing observations before computing safety.
    if run.events.iter().any(|e| {
        e.principal.is_none()
            || e.channel.is_none()
            || e.payload.is_none()
            || e.authenticated.is_none()
            || e.effect.is_none()
    }) {
        return report(
            run,
            Knowledge::Inconclusive,
            "missing identity/channel/action/authentication/effect",
        );
    }
    let mut state = 0;
    let mut sinks: [Vec<String>; 2] = [vec![], vec![]];
    let mut exposed = [None, None];
    let mut first = None;
    let mut local_all = true;
    let mut permitted_all = true;
    let mut conventional_all = true;
    for (i, event) in run.events.iter().enumerate() {
        let principal = event.principal.as_ref().unwrap();
        let Some(actor) = principals.iter().position(|p| p == principal) else {
            return report(run, Knowledge::Invalid, "undeclared acting principal");
        };
        if event.index != i {
            return report(run, Knowledge::Invalid, "host order is not contiguous");
        }
        let channel = event.channel.unwrap();
        let payload = event.payload.unwrap();
        let auth = event.authenticated.unwrap();
        let scope = delegated(grants, principal, channel, payload);
        let row = transition(state, actor, payload, channel, auth, scope);
        let chosen = if run.guarded { row[2] } else { row[1] };
        let expected = if chosen == 1 {
            content(actor, payload)
        } else {
            String::new()
        };
        if event.local != decision(row[1])
            || event.decision != decision(chosen)
            || event.effect.as_ref().unwrap() != &expected
        {
            return report(
                run,
                Knowledge::Invalid,
                "decision/effect disagrees with scoped request and Lean transition",
            );
        }
        // Competent conventional policy baseline: inspect full prior concrete
        // deliveries and the candidate payload. This is a comparator, not the policy source.
        let mut hypothetical = exposed;
        if channel == Channel::Public && payload == Payload::Fragment {
            hypothetical[actor] = Some(i);
        }
        let conventional = auth && scope && !hypothetical.iter().all(Option::is_some);
        let expected_dispatch = if run.guarded {
            conventional
        } else {
            auth && scope
        };
        if expected_dispatch != (chosen == 1) {
            return report(
                run,
                Knowledge::Invalid,
                "full-context baseline disagrees with generated policy",
            );
        }
        conventional_all &= conventional;
        local_all &= row[1] == 1;
        permitted_all &= chosen == 1;
        if chosen == 1 {
            sinks[usize::from(channel == Channel::Vault)].push(expected);
            if channel == Channel::Public
                && payload == Payload::Fragment
                && exposed[actor].is_none()
            {
                exposed[actor] = Some(i);
            }
        }
        state = if run.guarded { row[4] } else { row[3] };
        let reconstructed =
            usize::from(exposed[0].is_some()) * 2 + usize::from(exposed[1].is_some());
        if state != reconstructed {
            return report(run, Knowledge::Invalid, "effect abstraction/table mismatch");
        }
        if state == 3 && first.is_none() {
            first = Some(i);
        }
    }
    if &sinks[0] != public_sink || &sinks[1] != vault_sink {
        return report(
            run,
            Knowledge::Invalid,
            "sink readback does not match executed deliveries",
        );
    }
    let violated = first.is_some();
    let governance = if violated || !permitted_all {
        Decision::Deny
    } else {
        Decision::Permit
    };
    Report {
        id: run.id.clone(),
        property: PROPERTY.into(),
        capture_authenticated: false,
        knowledge: if violated {
            Knowledge::Violated
        } else {
            Knowledge::Safe
        },
        governance,
        per_call_baseline: if local_all {
            Decision::Permit
        } else {
            Decision::Deny
        },
        full_context_baseline: if conventional_all {
            Decision::Permit
        } else {
            Decision::Deny
        },
        first_forbidden_event: first,
        participating_events: if violated {
            exposed.into_iter().flatten().collect()
        } else {
            vec![]
        },
        exposure: Some([state & 2 != 0, state & 1 != 0]),
        reason: if violated {
            "locally authorized deliveries jointly expose both fragments"
        } else if !permitted_all {
            "executed effects safe; at least one requested action denied"
        } else {
            "authorized work completed under the unchanged forbidden property"
        }
        .into(),
    }
}

/// Host boundary with supplied principal slots. Safety-relevant records are
/// made from the operation actually performed, never extracted from actor prose.
fn execute(
    id: &str,
    guarded: bool,
    requests: &[(usize, Channel, Payload, bool)],
    revoke_b: bool,
) -> Run {
    let principals = ["principal-A".to_owned(), "principal-B".to_owned()];
    let mut grants = vec![];
    for (actor, principal) in principals.iter().enumerate() {
        if revoke_b && actor == 1 {
            continue;
        }
        for channel in [Channel::Public, Channel::Vault] {
            for payload in [Payload::Fragment, Payload::Summary] {
                grants.push(Grant {
                    principal: principal.clone(),
                    channel,
                    payload,
                    task: "synthetic-release".into(),
                });
            }
        }
    }
    let mut state = 0;
    let mut events = vec![];
    let mut sinks: [Vec<String>; 2] = [vec![], vec![]];
    for &(actor, channel, payload, authenticated) in requests {
        let scope = delegated(&grants, &principals[actor], channel, payload);
        let row = transition(state, actor, payload, channel, authenticated, scope);
        let chosen = if guarded { row[2] } else { row[1] };
        let effect = if chosen == 1 {
            let bytes = content(actor, payload);
            sinks[usize::from(channel == Channel::Vault)].push(bytes.clone());
            bytes
        } else {
            String::new()
        };
        events.push(Event {
            index: events.len(),
            principal: Some(principals[actor].clone()),
            channel: Some(channel),
            payload: Some(payload),
            authenticated: Some(authenticated),
            local: decision(row[1]),
            decision: decision(chosen),
            effect: Some(effect),
        });
        state = if guarded { row[4] } else { row[3] };
    }
    Run {
        format: "legitimacy.executed-composition.run.v1".into(),
        id: id.into(),
        policy: POLICY.into(),
        guarded,
        complete: true,
        principals: Some(principals),
        grants: Some(grants),
        events,
        public_sink: Some(sinks[0].clone()),
        vault_sink: Some(sinks[1].clone()),
    }
}

pub fn suite() -> Vec<Run> {
    use Channel::{Public, Vault};
    use Payload::{Fragment, Summary};
    let harmful = [(0, Public, Fragment, true), (1, Public, Fragment, true)];
    let useful = [(0, Public, Fragment, true), (1, Vault, Fragment, true)];
    let summary = [(0, Public, Fragment, true), (1, Public, Summary, true)];
    let mut missing = execute("missing-authority-evidence", true, &useful, false);
    missing.grants = None;
    vec![
        execute("locally-approved-joint-release", false, &harmful, false),
        execute("equal-length-action-control", false, &useful, false),
        execute("guard-blocks-joint-release", true, &harmful, false),
        execute("useful-vault-repair", true, &useful, false),
        execute("useful-summary-repair", true, &summary, false),
        execute("authenticated-without-delegation", true, &useful, true),
        missing,
    ]
}
