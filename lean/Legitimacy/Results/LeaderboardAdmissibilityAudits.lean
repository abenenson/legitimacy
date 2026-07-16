/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.CodexAdmissibilityAudit
import Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit
import Legitimacy.Results.ClaudeCodeAdmissibilityAudit
import Legitimacy.Results.GovernanceAdmissibilityAudit

/-!
# Legitimacy.Results.LeaderboardAdmissibilityAudits

Lean literals for committed extracted governance graphs. CrewAI and OpenClaw
remain leaderboard regression fixtures generated from
`audits/leaderboard/*-graph.json`; Codex, Claude Agent SDK, and Claude Code live
in dedicated theorem-backed modules whose public graph fixtures are under
`examples/graphs/`. The Lean governance-admissibility audit contract therefore
ranges over the same graph shape pinned by Rust byte-parity tests for each lane.

Codex, Claude Agent SDK, and Claude Code are isolated in dedicated modules so
their proof targets can be evaluated without elaborating the larger OpenClaw
literal. Those modules record the protocol-level governance-admissibility
status: under the current governance admissibility diagnostics, the committed
hook-protocol graphs evaluate to `AuditVerdict.rejected AuditCheck.monotonicity`.

CrewAI has the same structural failing check: its admissibility verdict evaluates to
`AuditVerdict.rejected AuditCheck.monotonicity`, and nonvacuity rejects terminal
escalation witnesses from the generated hook-gate claims. This frozen CrewAI
literal is test-source provenance: its nodes are extracted from
`lib/crewai/tests/hooks/test_tool_hooks.py`, not from the production
`lib/crewai/src/crewai` surface. The current OpenClaw
fixture differs: the committed leaderboard report records graph monotonicity as
passed and the live failing check as nonvacuity, because all examined claims reach
`Deny`. The dedicated theorem modules record these per-harness rejection facts
without adding more theorem declarations to this umbrella literal.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Lean audit literal of `audits/leaderboard/crewai-graph.json`. -/
def crewAIExtractedGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "lib/crewai/tests/hooks/test_tool_hooks.py::block_hook"
      "lib/crewai/tests/hooks/test_tool_hooks.py::block_hook:158-161"
      [ .exactMatch "dangerous_tool" .deny
        ]
      .permit
      .firstMatch
    , .binary "lib/crewai/tests/hooks/test_tool_hooks.py::blocking_before_hook"
      "lib/crewai/tests/hooks/test_tool_hooks.py::blocking_before_hook:764-772"
      [ .exactMatch "before" .deny
        , .exactMatch "tool_name" .deny
        , .exactMatch "tool_input" .deny
        , .exactMatch "dangerous_operation" .deny
        ]
      .permit
      .firstMatch
    , .binary "lib/crewai/tests/hooks/test_tool_hooks.py::test_first_blocking_hook_stops_execution"
      "lib/crewai/tests/hooks/test_tool_hooks.py::test_first_blocking_hook_stops_execution:340-376"
      [ .contentMatch "Test that first hook returning False blocks execution\\." .escalate
        , .exactMatch "test_tool" .escalate
        , .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    , .binary "lib/crewai/tests/hooks/test_tool_hooks.py::test_hooks_with_validation_and_sanitization"
      "lib/crewai/tests/hooks/test_tool_hooks.py::test_hooks_with_validation_and_sanitization:414-466"
      [ .thresholdGate "blocked_context" 1 .deny
        , .thresholdGate "hook" 1 .escalate
        , .contentMatch "Test a realistic scenario with validation and sanitization hooks\\." .escalate
        , .exactMatch "write_file" .escalate
        , .exactMatch "file_path" .escalate
        , .exactMatch ".env" .escalate
        , .exactMatch "read_file" .escalate
        , .exactMatch "config.txt" .escalate
        , .contentMatch "Content: SECRET_KEY=abc123" .escalate
        , .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    , .binary "lib/crewai/tests/hooks/test_tool_hooks.py::validate_file_path"
      "lib/crewai/tests/hooks/test_tool_hooks.py::validate_file_path:417-422"
      [ .exactMatch "write_file" .deny
        , .exactMatch "file_path" .deny
        , .exactMatch ".env" .deny
        ]
      .permit
      .firstMatch
    ]
  edges :=
    [ { fromNode := "lib/crewai/tests/hooks/test_tool_hooks.py::test_hooks_with_validation_and_sanitization", toNode := "lib/crewai/tests/hooks/test_tool_hooks.py::validate_file_path", transform := .passThrough }
    ]

/-- CrewAI extracted-graph audit subject using the production Lean evaluator. -/
def crewAIExtractedGraph : AuditSubject where
  graph := crewAIExtractedGovernanceGraph
  evalNode := auditEvaluateNode

/-- Lean audit literal of `audits/leaderboard/openclaw-graph.json`. -/
def openClawInfraExtractedGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "approval-errors.ts::isapprovalnotfounderror"
      "approval-errors.ts::isapprovalnotfounderror:18-31"
      [ .thresholdGate "approval_not_found" 1 .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-gateway-resolver.ts::resolveapprovalovergateway"
      "approval-gateway-resolver.ts::resolveapprovalovergateway:16-79"
      [ .thresholdGate "allowpluginfallback" 1 .permit
        , .thresholdGate "approvalid" 1 .permit
        , .contentMatch "Approval \\(\\$\\{params\\.senderId\\?\\.trim\\(\\) \\|\\| \"unknown\"\\}\\)" .escalate
        , .exactMatch "unknown" .escalate
        , .exactMatch "plugin:" .escalate
        , .exactMatch "plugin.approval.resolve" .escalate
        , .exactMatch "exec.approval.resolve" .escalate
        ]
      .permit
      .firstMatch
    , .binary "approval-handler-bootstrap.ts::startchannelapprovalhandlerbootstrap"
      "approval-handler-bootstrap.ts::startchannelapprovalhandlerbootstrap:19-167"
      [ .prefixMatch "${params.plugin.id}/approval-bootstrap" .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-handler-bootstrap.ts::starthandlerforcontext"
      "approval-handler-bootstrap.ts::starthandlerforcontext:56-91"
      [ .prefixMatch "${params.plugin.id}/native-approvals" .permit
        , .contentMatch "\\$\\{channelLabel\\} Native Approvals \\(\\$\\{params\\.accountId\\}\\)" .permit
        , .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    , .binary "approval-handler-runtime.ts::createchannelapprovalhandlerfromcapability"
      "approval-handler-runtime.ts::createchannelapprovalhandlerfromcapability:468-716"
      [ .exactMatch "string" .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-native-delivery.ts::resolvechannelnativeapprovaldeliveryplan"
      "approval-native-delivery.ts::resolvechannelnativeapprovaldeliveryplan:42-131"
      [ .exactMatch "origin" .permit
        , .exactMatch "both" .permit
        , .exactMatch "approver-dm" .permit
        , .exactMatch "preferred" .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-native-route-coordinator.ts::maybefinalizeapprovalroutenotice"
      "approval-native-route-coordinator.ts::maybefinalizeapprovalroutenotice:240-274"
      [ .exactMatch "send" .permit
        , .contentMatch "approval\\-route\\-notice:\\$\\{approvalId\\}" .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-native-route-coordinator.ts::observerequest"
      "approval-native-route-coordinator.ts::observerequest:318-333"
      [ .thresholdGate "approvalkind" 1 .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-native-route-coordinator.ts::report"
      "approval-native-route-coordinator.ts::report:286-315"
      [ .thresholdGate "approvalkind" 1 .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-native-route-notice.ts::resolveapprovalroutedelsewherenoticetext"
      "approval-native-route-notice.ts::resolveapprovalroutedelsewherenoticetext:26-38"
      [ .contentMatch "Approval required\\. I sent the approval request to \\$\\{formatHumanList\\(\n    uniqueDestinations\\.toSorted\\(\\(a, b\\) => a\\.localeCompare\\(b\\)\\),\n  \\)\\}, not this chat\\." .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-native-runtime.ts::deliverapprovalrequestviachannelnativeplan"
      "approval-native-runtime.ts::deliverapprovalrequestviachannelnativeplan:35-135"
      [ .exactMatch "string" .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-turn-source.ts::hasapprovalturnsourceroute"
      "approval-turn-source.ts::hasapprovalturnsourceroute:4-18"
      [ .exactMatch "enabled" .deny
        ]
      .permit
      .firstMatch
    , .binary "approval-view-model.ts::buildexecmetadata"
      "approval-view-model.ts::buildexecmetadata:21-36"
      [ .exactMatch "Agent" .permit
        , .exactMatch "CWD" .permit
        , .exactMatch "Host" .permit
        , .contentMatch "Env Overrides" .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-view-model.ts::buildpendingapprovalview"
      "approval-view-model.ts::buildpendingapprovalview:99-120"
      [ .exactMatch "plugin:" .permit
        , .exactMatch "pending" .permit
        ]
      .deny
      .firstMatch
    , .binary "approval-view-model.ts::buildpluginmetadata"
      "approval-view-model.ts::buildpluginmetadata:38-55"
      [ .exactMatch "warning" .permit
        , .exactMatch "Severity" .permit
        , .exactMatch "critical" .permit
        , .exactMatch "Critical" .permit
        , .exactMatch "info" .permit
        , .exactMatch "Info" .permit
        , .exactMatch "Warning" .permit
        , .exactMatch "Tool" .permit
        ]
      .deny
      .firstMatch
    , .binary "channel-approval-auth.ts::resolveapprovalcommandauthorization"
      "channel-approval-auth.ts::resolveapprovalcommandauthorization:12-50"
      [ .exactMatch "approve" .permit
        , .exactMatch "disabled" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approval-channel-runtime.ts::anonymous_callback_226"
      "exec-approval-channel-runtime.ts::anonymous_callback_226:226-300"
      [ .exactMatch "disabled" .deny
        , .thresholdGate "hook_registration" 1 .escalate
        ]
      .permit
      .firstMatch
    , .binary "exec-approval-channel-runtime.ts::handleexpired"
      "exec-approval-channel-runtime.ts::handleexpired:95-105"
      [ .contentMatch "expired \\$\\{approvalId\\}" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approval-channel-runtime.ts::handlerequested"
      "exec-approval-channel-runtime.ts::handlerequested:107-168"
      [ .contentMatch "ignored duplicate request \\$\\{request\\.id\\}" .permit
        , .contentMatch "received request \\$\\{request\\.id\\}" .permit
        , .contentMatch "resolved \\$\\{entry\\.pendingResolution\\.id\\} with \\$\\{entry\\.pendingResolution\\.decision\\}" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approval-forwarder.ts::buildrequestmessage"
      "exec-approval-forwarder.ts::buildrequestmessage:224-272"
      [ .thresholdGate "alloweddecisions" 1 .permit
        , .contentMatch "\\|" .permit
        , .exactMatch "string" .permit
        , .contentMatch "🔒 Exec approval required" .permit
        , .contentMatch "ID: \\$\\{request\\.id\\}" .permit
        , .contentMatch "Command: \\$\\{command\\.text\\}" .permit
        , .exactMatch "Command:" .permit
        , .contentMatch "CWD: \\$\\{request\\.request\\.cwd\\}" .permit
        , .contentMatch "Node: \\$\\{request\\.request\\.nodeId\\}" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approval-reply.ts::buildexecapprovalactiondescriptors"
      "exec-approval-reply.ts::buildexecapprovalactiondescriptors:119-164"
      [ .thresholdGate "alloweddecisions" 1 .permit
        , .thresholdGate "approvalcommandid" 1 .permit
        , .exactMatch "allow-once" .escalate
        , .contentMatch "Allow Once" .escalate
        , .exactMatch "success" .escalate
        , .exactMatch "allow-always" .escalate
        , .contentMatch "Allow Always" .escalate
        ]
      .permit
      .firstMatch
    , .binary "exec-approval-reply.ts::buildexecapprovalpendingreplypayload"
      "exec-approval-reply.ts::buildexecapprovalpendingreplypayload:298-364"
      [ .thresholdGate "alloweddecisions" 1 .permit
        , .exactMatch "string" .permit
        , .contentMatch "Approval required\\." .permit
        , .exactMatch "Run:" .permit
        , .exactMatch "txt" .permit
        , .contentMatch "Pending command:" .permit
        , .exactMatch "sh" .permit
        , .contentMatch "Other options:" .permit
        , .exactMatch "allow-always" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approval-reply.ts::getexecapprovalreplymetadata"
      "exec-approval-reply.ts::getexecapprovalreplymetadata:262-296"
      [ .thresholdGate "approvalid" 1 .permit
        , .thresholdGate "approvalslug" 1 .permit
        , .exactMatch "object" .permit
        , .exactMatch "string" .permit
        , .exactMatch "plugin" .permit
        , .exactMatch "exec" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approval-reply.ts::parseexecapprovalcommandtext"
      "exec-approval-reply.ts::parseexecapprovalcommandtext:213-229"
      [ .exactMatch "always" .permit
        , .exactMatch "allow-always" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approval-surface.ts::resolveexecapprovalinitiatingsurfacestate"
      "exec-approval-surface.ts::resolveexecapprovalinitiatingsurfacestate:40-73"
      [ .exactMatch "tui" .permit
        , .exactMatch "enabled" .permit
        , .exactMatch "approve" .permit
        , .exactMatch "exec" .permit
        , .exactMatch "unsupported" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approval-surface.ts::supportsnativeexecapprovalclient"
      "exec-approval-surface.ts::supportsnativeexecapprovalclient:75-81"
      [ .exactMatch "tui" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::evaluateshellallowlist"
      "exec-approvals-allowlist.ts::evaluateshellallowlist:1079-1221"
      [ .thresholdGate "allowlistsatisfied" 1 .permit
        , .thresholdGate "allowskillpreludeatindex" 1 .permit
        , .exactMatch "string" .permit
        , .contentMatch "\\&\\&" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::evaluateshellwrapperinlinechain"
      "exec-approvals-allowlist.ts::evaluateshellwrapperinlinechain:544-579"
      [ .exactMatch "allowlist" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::isdirectshellpositionalcarrierinvocation"
      "exec-approvals-allowlist.ts::isdirectshellpositionalcarrierinvocation:858-871"
      [ .contentMatch "\\[\\^\\\\S\\\\r\\\\n\\]\\+" .deny
        , .contentMatch "\\(\\?:\\\\\\$\\(\\?:0\\|\\\\\\{0\\\\\\}\\)\\|\"\\\\\\$\\(\\?:0\\|\\\\\\{0\\\\\\}\\)\"\\)" .deny
        , .contentMatch "\\(\\?:\\\\\\$\\(\\?:\\[@\\*\\]\\|\\[1\\-9\\]\\|\\\\\\{\\[@\\*1\\-9\\]\\\\\\}\\)\\|\"\\\\\\$\\(\\?:\\[@\\*\\]\\|\\[1\\-9\\]\\|\\\\\\{\\[@\\*1\\-9\\]\\\\\\}\\)\"\\)" .deny
        , .contentMatch "\\^\\(\\?:exec\\$\\{shellWhitespace\\}\\(\\?:\\-\\-\\$\\{shellWhitespace\\}\\)\\?\\)\\?\\$\\{positionalZero\\}\\(\\?:\\$\\{shellWhitespace\\}\\$\\{positionalArg\\}\\)\\*\\$" .deny
        , .exactMatch "u" .deny
        ]
      .permit
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::isskillautoallowedsegment"
      "exec-approvals-allowlist.ts::isskillautoallowedsegment:193-216"
      [ .thresholdGate "allowskills" 1 .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::isskillmarkdownpreludepath"
      "exec-approvals-allowlist.ts::isskillmarkdownpreludepath:226-246"
      [ .prefixMatch "/" .deny
        , .prefixMatch "/skill.md" .deny
        , .exactMatch "skills" .deny
        ]
      .permit
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::isskillpreludemarkersegment"
      "exec-approvals-allowlist.ts::isskillpreludemarkersegment:288-298"
      [ .exactMatch "printf" .deny
        , .contentMatch "\\\\\\\\n\\-\\-\\-CMD\\-\\-\\-\\\\\\\\n" .deny
        , .contentMatch "\\\\n\\-\\-\\-CMD\\-\\-\\-\\\\n" .deny
        ]
      .permit
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::isskillpreludereadsegment"
      "exec-approvals-allowlist.ts::isskillpreludereadsegment:271-286"
      [ .exactMatch "cat" .deny
        ]
      .permit
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::resolvesegmentsatisfaction"
      "exec-approvals-allowlist.ts::resolvesegmentsatisfaction:493-521"
      [ .exactMatch "allowlist" .permit
        , .exactMatch "safeBins" .permit
        , .exactMatch "skills" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::resolveshellwrapperpositionalargvcandidatepath"
      "exec-approvals-allowlist.ts::resolveshellwrapperpositionalargvcandidatepath:812-856"
      [ .exactMatch "ash" .permit
        , .exactMatch "bash" .permit
        , .exactMatch "dash" .permit
        , .exactMatch "fish" .permit
        , .exactMatch "ksh" .permit
        , .exactMatch "sh" .permit
        , .exactMatch "zsh" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals-allowlist.ts::segments.every_handler_callback_596"
      "exec-approvals-allowlist.ts::segments.every_handler_callback_596:596-633"
      [ .thresholdGate "policyblocked" 1 .escalate
        ]
      .permit
      .firstMatch
    , .binary "exec-approvals-analysis.ts::splitcommandchainwithoperators"
      "exec-approvals-analysis.ts::splitcommandchainwithoperators:617-726"
      [ .contentMatch "\\\\\\\\" .escalate
        , .contentMatch "\"" .escalate
        , .contentMatch "\\&" .escalate
        , .contentMatch "\\&\\&" .escalate
        ]
      .permit
      .firstMatch
    , .binary "exec-approvals-analysis.ts::splitshellpipeline"
      "exec-approvals-analysis.ts::splitshellpipeline:81-354"
      [ .exactMatch "string" .escalate
        , .contentMatch "\\\\n" .escalate
        , .contentMatch "\\\\r" .escalate
        , .contentMatch "command substitution in unquoted heredoc" .escalate
        , .contentMatch "\\\\\\\\" .escalate
        ]
      .permit
      .firstMatch
    , .binary "exec-approvals.ts::coerceallowlistentries"
      "exec-approvals.ts::coerceallowlistentries:283-310"
      [ .thresholdGate "allowlist" 1 .permit
        , .exactMatch "string" .permit
        , .exactMatch "object" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals.ts::ensureallowlistids"
      "exec-approvals.ts::ensureallowlistids:312-327"
      [ .thresholdGate "allowlist" 1 .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals.ts::requiresexecapproval"
      "exec-approvals.ts::requiresexecapproval:772-790"
      [ .exactMatch "always" .permit
        , .exactMatch "on-miss" .permit
        , .exactMatch "allowlist" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals.ts::resolveexecapprovalalloweddecisions"
      "exec-approvals.ts::resolveexecapprovalalloweddecisions:1017-1025"
      [ .exactMatch "always" .escalate
        , .exactMatch "allow-once" .escalate
        , .exactMatch "deny" .escalate
        ]
      .permit
      .firstMatch
    , .binary "exec-approvals.ts::stripallowlistcommandtext"
      "exec-approvals.ts::stripallowlistcommandtext:329-345"
      [ .thresholdGate "allowlist" 1 .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-approvals.ts::writeexecapprovalsraw"
      "exec-approvals.ts::writeexecapprovalsraw:487-506"
      [ .contentMatch "\\.exec\\-approvals\\.\\$\\{process\\.pid\\}\\.\\$\\{crypto\\.randomUUID\\(\\)\\}\\.tmp" .permit
        , .exactMatch "wx" .permit
        ]
      .deny
      .firstMatch
    , .binary "exec-safe-bin-policy-validator.ts::ispathliketoken"
      "exec-safe-bin-policy-validator.ts::ispathliketoken:9-24"
      [ .exactMatch "-" .deny
        , .prefixMatch "./" .deny
        , .prefixMatch "../" .deny
        , .prefixMatch "/" .deny
        ]
      .permit
      .firstMatch
    , .binary "exec-safe-bin-policy-validator.ts::issafeliteraltoken"
      "exec-safe-bin-policy-validator.ts::issafeliteraltoken:34-39"
      [ .exactMatch "-" .permit
        ]
      .deny
      .firstMatch
    , .binary "net/fetch-guard.ts::fetchwithssrfguard"
      "net/fetch-guard.ts::fetchwithssrfguard:282-450"
      [ .contentMatch "fetch is not available" .escalate
        , .exactMatch "number" .escalate
        , .exactMatch "string" .escalate
        , .contentMatch "Invalid URL: must be http or https" .escalate
        , .exactMatch "http:" .escalate
        , .exactMatch "https:" .escalate
        , .exactMatch "explicit-proxy" .escalate
        ]
      .permit
      .firstMatch
    , .binary "net/fetch-guard.ts::rewriteredirectinitforcrossorigin"
      "net/fetch-guard.ts::rewriteredirectinitforcrossorigin:259-278"
      [ .thresholdGate "allowunsafereplay" 1 .permit
        , .exactMatch "GET" .permit
        , .exactMatch "HEAD" .permit
        ]
      .deny
      .firstMatch
    , .binary "outbound/outbound-policy.ts::enforcecrosscontextpolicy"
      "outbound/outbound-policy.ts::enforcecrosscontextpolicy:91-141"
      [ .thresholdGate "allowacrossproviders" 1 .permit
        , .thresholdGate "allowcrosscontextsend" 1 .permit
        , .thresholdGate "allowwithinprovider" 1 .permit
        , .contentMatch "Cross\\-context messaging denied: action=\\$\\{params\\.action\\} target provider \"\\$\\{params\\.channel\\}\" while bound to \"\\$\\{currentProvider\\}\"\\." .permit
        , .contentMatch "Cross\\-context messaging denied: action=\\$\\{params\\.action\\} target=\"\\$\\{target\\}\" while bound to \"\\$\\{currentTarget\\}\" \\(channel=\\$\\{params\\.channel\\}\\)\\." .permit
        ]
      .deny
      .firstMatch
    , .binary "path-alias-guards.ts::assertnopathaliasescape"
      "path-alias-guards.ts::assertnopathaliasescape:12-34"
      [ .thresholdGate "allowfinalsymlink" 1 .permit
        , .exactMatch "symlink" .permit
        ]
      .deny
      .firstMatch
    , .binary "plugin-approvals.ts::approvaldecisionlabel"
      "plugin-approvals.ts::approvaldecisionlabel:38-46"
      [ .exactMatch "allow-once" .permit
        , .contentMatch "allowed once" .permit
        , .exactMatch "allow-always" .permit
        , .contentMatch "allowed always" .permit
        , .exactMatch "denied" .permit
        ]
      .deny
      .firstMatch
    , .binary "runtime-guard.ts::runtimesatisfies"
      "runtime-guard.ts::runtimesatisfies:65-71"
      [ .exactMatch "node" .deny
        ]
      .permit
      .firstMatch
    , .binary "system-run-approval-binding.ts::matchsystemrunapprovalenvhash"
      "system-run-approval-binding.ts::matchsystemrunapprovalenvhash:160-199"
      [ .exactMatch "APPROVAL_ENV_BINDING_MISSING" .permit
        , .contentMatch "approval id missing env binding for requested env overrides" .permit
        , .exactMatch "APPROVAL_ENV_MISMATCH" .permit
        , .contentMatch "approval id env binding mismatch" .permit
        ]
      .deny
      .firstMatch
    ]
  edges :=
    [ { fromNode := "approval-gateway-resolver.ts::resolveapprovalovergateway", toNode := "approval-errors.ts::isapprovalnotfounderror", transform := .passThrough }
    , { fromNode := "approval-handler-bootstrap.ts::startchannelapprovalhandlerbootstrap", toNode := "approval-handler-bootstrap.ts::starthandlerforcontext", transform := .passThrough }
    , { fromNode := "approval-handler-bootstrap.ts::starthandlerforcontext", toNode := "approval-handler-runtime.ts::createchannelapprovalhandlerfromcapability", transform := .passThrough }
    , { fromNode := "approval-native-route-coordinator.ts::report", toNode := "approval-native-route-coordinator.ts::maybefinalizeapprovalroutenotice", transform := .passThrough }
    , { fromNode := "approval-native-runtime.ts::deliverapprovalrequestviachannelnativeplan", toNode := "approval-native-delivery.ts::resolvechannelnativeapprovaldeliveryplan", transform := .passThrough }
    , { fromNode := "approval-turn-source.ts::hasapprovalturnsourceroute", toNode := "exec-approval-surface.ts::resolveexecapprovalinitiatingsurfacestate", transform := .passThrough }
    , { fromNode := "approval-view-model.ts::buildpendingapprovalview", toNode := "exec-approval-reply.ts::buildexecapprovalactiondescriptors", transform := .passThrough }
    , { fromNode := "exec-approval-channel-runtime.ts::anonymous_callback_226", toNode := "exec-approval-channel-runtime.ts::handlerequested", transform := .passThrough }
    , { fromNode := "exec-approval-reply.ts::buildexecapprovalpendingreplypayload", toNode := "exec-approval-reply.ts::buildexecapprovalactiondescriptors", transform := .passThrough }
    , { fromNode := "exec-approvals-allowlist.ts::isskillpreludereadsegment", toNode := "exec-approvals-allowlist.ts::isskillmarkdownpreludepath", transform := .passThrough }
    , { fromNode := "exec-approvals-allowlist.ts::resolvesegmentsatisfaction", toNode := "exec-approvals-allowlist.ts::isskillautoallowedsegment", transform := .passThrough }
    , { fromNode := "exec-approvals-allowlist.ts::segments.every_handler_callback_596", toNode := "exec-approvals-allowlist.ts::resolvesegmentsatisfaction", transform := .passThrough }
    , { fromNode := "exec-approvals-allowlist.ts::resolveshellwrapperpositionalargvcandidatepath", toNode := "exec-approvals-allowlist.ts::isdirectshellpositionalcarrierinvocation", transform := .passThrough }
    , { fromNode := "exec-approvals-allowlist.ts::evaluateshellallowlist", toNode := "exec-approvals-analysis.ts::splitcommandchainwithoperators", transform := .passThrough }
    , { fromNode := "exec-safe-bin-policy-validator.ts::issafeliteraltoken", toNode := "exec-safe-bin-policy-validator.ts::ispathliketoken", transform := .passThrough }
    , { fromNode := "net/fetch-guard.ts::fetchwithssrfguard", toNode := "net/fetch-guard.ts::rewriteredirectinitforcrossorigin", transform := .passThrough }
    ]

/-- Audit OpenClaw infrastructure extracted-graph audit subject using the production Lean evaluator. -/
def openClawInfraExtractedGraph : AuditSubject where
  graph := openClawInfraExtractedGovernanceGraph
  evalNode := auditEvaluateNode

end Legitimacy
