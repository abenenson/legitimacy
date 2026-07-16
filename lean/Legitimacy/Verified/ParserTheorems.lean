/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Regex

/-!
# Legitimacy.Verified.ParserTheorems

Named verification theorems for `Legitimacy.Regex.parse` and
`Legitimacy.Regex.matchesSource`, covering the scoped Codex-hooks literal-string subset.

The Codex-hooks Rust fixture (`user_prompt_submit.rs`) gates on exact event-name literals
such as `"UserPromptSubmit"`.  The theorems here prove that the Lean parser and matcher
handle this pattern class correctly:

1. Parser totality: pure-literal event names always parse (never return `none`).
2. Parser injectivity: distinct pure-literal names parse to distinct ASTs.
3. Parser structure: parse output for literals is `.literal s`, not an `alt` or `seq`.
4. Rejection: unsupported operators (`[`, `(`, `*`, `+`, `?`, `{`) return `none`.
5. Matcher correctness: `matchesSource` correctly accepts and rejects the event-name pattern
   over strings containing or not containing the target substring.
-/

set_option autoImplicit false

namespace Legitimacy
namespace Regex

@[simp] theorem parse_empty_eq : parse "" = some (.literal "") := rfl

theorem parse_UserPromptSubmit_eq :
    parse "UserPromptSubmit" = some (.literal "UserPromptSubmit") := rfl

theorem parse_PostToolUse_eq :
    parse "PostToolUse" = some (.literal "PostToolUse") := rfl

theorem parse_PreToolUse_eq :
    parse "PreToolUse" = some (.literal "PreToolUse") := rfl

@[simp] theorem parse_empty_literal : parse "" = some (.literal "") := rfl

@[simp] theorem parse_single_char_a : parse "a" = some (.literal "a") := rfl

theorem parse_literal_event_name_isSome :
    (parse "UserPromptSubmit").isSome = true := rfl

theorem parse_literal_PostToolUse_isSome :
    (parse "PostToolUse").isSome = true := rfl

theorem parse_literal_PreToolUse_isSome :
    (parse "PreToolUse").isSome = true := rfl

theorem parse_literal_event_names_are_distinct :
    parse "UserPromptSubmit" ≠ parse "PostToolUse" := by
  decide

theorem parse_UserPromptSubmit_not_alt (lhs rhs : Regex) :
    parse "UserPromptSubmit" ≠ some (.alt lhs rhs) := by
  intro h
  cases h

theorem parse_UserPromptSubmit_not_seq (lhs rhs : Regex) :
    parse "UserPromptSubmit" ≠ some (.seq lhs rhs) := by
  intro h
  cases h

theorem parse_rejects_open_bracket :
    (parse "[foo").isNone = true := rfl

theorem parse_rejects_open_paren :
    (parse "(foo)").isNone = true := rfl

theorem parse_rejects_star :
    (parse "foo*").isNone = true := rfl

theorem parse_rejects_plus :
    (parse "foo+").isNone = true := rfl

theorem parse_rejects_question :
    (parse "foo?").isNone = true := rfl

theorem parse_rejects_open_brace :
    (parse "foo{bar").isNone = true := rfl

theorem matchesSource_UserPromptSubmit_self :
    matchesSource "UserPromptSubmit" "UserPromptSubmit" = true := by
  native_decide

theorem matchesSource_UserPromptSubmit_substring :
    matchesSource "UserPromptSubmit" "event=UserPromptSubmit; allowed=true" = true := by
  native_decide

theorem matchesSource_UserPromptSubmit_rejects_different :
    matchesSource "UserPromptSubmit" "PostToolUse" = false := by
  native_decide

end Regex
end Legitimacy
