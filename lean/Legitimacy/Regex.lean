/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# Legitimacy.Regex

Lean regex support for the shipped `ContentMatch` corpus.

## Main Result

* `Regex.parse` accepts the regex surface exercised by the committed
  leaderboard graphs: literals, backslash escapes, `^`, `$`, alternation, and
  concatenation.
* `Regex.matches` compiles parsed regexes to a Thompson-style epsilon-NFA and
  evaluates them with Rust `regex::Regex::is_match` substring semantics.
* Unsupported active operators still return `none` from `Regex.parse`.
-/
set_option autoImplicit false

namespace Legitimacy

/-- Supported positional anchors in the shipped regex surface. -/
inductive RegexAnchor where
  | start
  | finish
  deriving Repr, DecidableEq

/-- Regex AST for the shipped `ContentMatch` surface. -/
inductive Regex where
  | literal (value : String)
  | anchor (pos : RegexAnchor)
  | alt (lhs rhs : Regex)
  | seq (lhs rhs : Regex)
  deriving Repr, DecidableEq

namespace Regex

/-- Transition labels for the Thompson NFA used by `Regex.matches`. -/
inductive RegexLabel where
  | epsilon
  | char (value : Char)
  | start
  | finish
  deriving Repr, DecidableEq

/-- A single NFA transition. -/
structure RegexTransition where
  source : Nat
  label : RegexLabel
  target : Nat
  deriving Repr, DecidableEq

/-- Compiled Thompson NFA for the shipped regex surface. -/
structure RegexAutomaton where
  start : Nat
  accept : Nat
  nextState : Nat
  transitions : List RegexTransition
  deriving Repr, DecidableEq

private def flushLiteral (literalRev : List Char) (atomsRev : List Regex) : List Regex :=
  if literalRev.isEmpty then
    atomsRev
  else
    .literal (String.ofList literalRev.reverse) :: atomsRev

private def branchRegex : List Regex → Regex
  | [] => .literal ""
  | [atom] => atom
  | atom :: tail => .seq atom (branchRegex tail)

private def altRegex : List Regex → Regex
  | [] => .literal ""
  | [branch] => branch
  | branch :: tail => .alt branch (altRegex tail)

private def parseBranches :
    List Char → List Regex → List Char → List (List Regex) → Option (List (List Regex))
  | [], atomsRev, literalRev, branchesRev =>
      let branch := (flushLiteral literalRev atomsRev).reverse
      some ((branch :: branchesRev).reverse)
  | '\\' :: [], _, _, _ => none
  | '\\' :: next :: tail, atomsRev, literalRev, branchesRev =>
      parseBranches tail atomsRev (next :: literalRev) branchesRev
  | '|' :: tail, atomsRev, literalRev, branchesRev =>
      let branch := (flushLiteral literalRev atomsRev).reverse
      parseBranches tail [] [] (branch :: branchesRev)
  | '^' :: tail, atomsRev, literalRev, branchesRev =>
      let atomsRev := Regex.anchor .start :: flushLiteral literalRev atomsRev
      parseBranches tail atomsRev [] branchesRev
  | '$' :: tail, atomsRev, literalRev, branchesRev =>
      let atomsRev := Regex.anchor .finish :: flushLiteral literalRev atomsRev
      parseBranches tail atomsRev [] branchesRev
  | '[' :: _, _, _, _ => none
  | ']' :: _, _, _, _ => none
  | '(' :: _, _, _, _ => none
  | ')' :: _, _, _, _ => none
  | '*' :: _, _, _, _ => none
  | '+' :: _, _, _, _ => none
  | '?' :: _, _, _, _ => none
  | '{' :: _, _, _, _ => none
  | '}' :: _, _, _, _ => none
  | ch :: tail, atomsRev, literalRev, branchesRev =>
      parseBranches tail atomsRev (ch :: literalRev) branchesRev

/-- Parse a shipped `ContentMatch` regex. Unsupported active operators return
`none`. -/
def parse (source : String) : Option Regex := do
  let branches <- parseBranches source.toList [] [] []
  pure <| altRegex (branches.map branchRegex)

private def insertUnique {α : Type} [DecidableEq α] (value : α) (values : List α) : List α :=
  if value ∈ values then values else value :: values

private def unionUnique {α : Type} [DecidableEq α] (lhs rhs : List α) : List α :=
  rhs.foldl (fun acc value => insertUnique value acc) lhs

private def compileLiteralTail :
    List Char → Nat → Nat → Nat × List RegexTransition
  | [], state, _ => (state, [])
  | ch :: tail, state, nextState =>
      let target := nextState
      let transition : RegexTransition :=
        { source := state, label := .char ch, target := target }
      let (accept, tailTransitions) := compileLiteralTail tail target (nextState + 1)
      (accept, transition :: tailTransitions)

private def compileLiteral (value : String) (nextState : Nat) : RegexAutomaton :=
  match value.toList with
  | [] =>
      let start := nextState
      let accept := nextState + 1
      { start := start
        accept := accept
        nextState := nextState + 2
        transitions :=
          [{ source := start, label := .epsilon, target := accept }] }
  | ch :: tail =>
      let start := nextState
      let firstTarget := nextState + 1
      let first : RegexTransition :=
        { source := start, label := .char ch, target := firstTarget }
      let (accept, tailTransitions) := compileLiteralTail tail firstTarget (nextState + 2)
      { start := start
        accept := accept
        nextState := accept + 1
        transitions := first :: tailTransitions }

private def compileAnchor (pos : RegexAnchor) (nextState : Nat) : RegexAutomaton :=
  let start := nextState
  let accept := nextState + 1
  let label :=
    match pos with
    | .start => RegexLabel.start
    | .finish => RegexLabel.finish
  { start := start
    accept := accept
    nextState := nextState + 2
    transitions := [{ source := start, label := label, target := accept }] }

private def compile : Regex → Nat → RegexAutomaton
  | .literal value, nextState => compileLiteral value nextState
  | .anchor pos, nextState => compileAnchor pos nextState
  | .seq lhs rhs, nextState =>
      let lhsAutomaton := compile lhs nextState
      let rhsAutomaton := compile rhs lhsAutomaton.nextState
      { start := lhsAutomaton.start
        accept := rhsAutomaton.accept
        nextState := rhsAutomaton.nextState
        transitions :=
          lhsAutomaton.transitions ++
            [{ source := lhsAutomaton.accept, label := .epsilon, target := rhsAutomaton.start }] ++
            rhsAutomaton.transitions }
  | .alt lhs rhs, nextState =>
      let start := nextState
      let accept := nextState + 1
      let lhsAutomaton := compile lhs (nextState + 2)
      let rhsAutomaton := compile rhs lhsAutomaton.nextState
      { start := start
        accept := accept
        nextState := rhsAutomaton.nextState
        transitions :=
          [{ source := start, label := .epsilon, target := lhsAutomaton.start },
           { source := start, label := .epsilon, target := rhsAutomaton.start }] ++
            lhsAutomaton.transitions ++
            rhsAutomaton.transitions ++
            [{ source := lhsAutomaton.accept, label := .epsilon, target := accept },
             { source := rhsAutomaton.accept, label := .epsilon, target := accept }] }

private def zeroWidthEnabled (label : RegexLabel) (input suffix : List Char) : Bool :=
  match label with
  | .epsilon => true
  | .start => suffix = input
  | .finish => suffix.isEmpty
  | .char _ => false

private def zeroWidthTargets
    (automaton : RegexAutomaton)
    (input suffix : List Char)
    (state : Nat) :
    List Nat :=
  automaton.transitions.foldl (fun acc transition =>
    if transition.source = state && zeroWidthEnabled transition.label input suffix then
      insertUnique transition.target acc
    else
      acc) []

private def charTargets (automaton : RegexAutomaton) (state : Nat) (ch : Char) : List Nat :=
  automaton.transitions.foldl (fun acc transition =>
    match transition.label with
    | .char value =>
        if transition.source = state && value = ch then
          insertUnique transition.target acc
        else
          acc
    | .epsilon | .start | .finish => acc) []

private def closeStates
    (automaton : RegexAutomaton)
    (input suffix : List Char) :
    Nat → List Nat → List Nat
  | 0, states => states
  | fuel + 1, states =>
      let next := states.foldl (fun acc state =>
        unionUnique acc (zeroWidthTargets automaton input suffix state)) states
      if next.length = states.length then
        states
      else
        closeStates automaton input suffix fuel next

private def advanceStates (automaton : RegexAutomaton) (states : List Nat) (ch : Char) :
    List Nat :=
  states.foldl (fun acc state => unionUnique acc (charTargets automaton state ch)) []

private def matchesSuffix
    (automaton : RegexAutomaton)
    (input : List Char) :
    List Char → List Nat → Bool
  | suffix, states =>
      let closed := closeStates automaton input suffix automaton.nextState states
      if automaton.accept ∈ closed then
        true
      else
        match suffix with
        | [] => false
        | ch :: tail =>
            let nextStates := advanceStates automaton closed ch
            if nextStates.isEmpty then
              false
            else
              matchesSuffix automaton input tail nextStates

private def suffixes : List Char → List (List Char)
  | [] => [[]]
  | chars@(_ :: tail) => chars :: suffixes tail

/-- Match a compiled regex against an input string using substring semantics,
like Rust `regex::Regex::is_match`. -/
def «matches» (regex : Regex) (input : String) : Bool :=
  let chars := input.toList
  let automaton := compile regex 0
  (suffixes chars).any fun suffix => matchesSuffix automaton chars suffix [automaton.start]

/-- Parse and match a shipped regex. Unsupported active operators return
`none`. -/
def matchesSource? (source input : String) : Option Bool := do
  let regex <- parse source
  pure <| Regex.matches regex input

/-- Parse and match a shipped regex. Unsupported active operators return
`false`. -/
def matchesSource (source input : String) : Bool :=
  (matchesSource? source input).getD false

example : parse "foo" = some (.literal "foo") := rfl

example :
    parse "^foo$" =
      some (.seq (.anchor .start) (.seq (.literal "foo") (.anchor .finish))) := rfl

example :
    parse "foo|bar" = some (.alt (.literal "foo") (.literal "bar")) := rfl

example : parse "foo[bar" = none := rfl

-- native_decide: finite literal regex/parser acceptance checks over concrete strings.
example : matchesSource "foo" "safe foo content" = true := by native_decide

example : matchesSource "^foo" "foobar" = true := by native_decide

example : matchesSource "^foo" "barfoo" = false := by native_decide

example : matchesSource "foo$" "barfoo" = true := by native_decide

example : matchesSource "foo|bar" "contains bar" = true := by native_decide

example : matchesSource "foo\\|bar" "safe foo|bar content" = true := by native_decide

example : matchesSource "\\\\n" "escaped \\n marker" = true := by native_decide

example : matchesSource "foo$bar" "foo\nbar" = false := by native_decide

example : matchesSource "\\[\\^\\\\S\\\\r\\\\n\\]\\+" "[^\\\\S\\\\r\\\\n]+" = false := by
  native_decide

example :
    matchesSource
        "Approval \\(\\$\\{params\\.senderId\\?\\.trim\\(\\) \\|\\| \"unknown\"\\}\\)"
        "Approval (${params.senderId?.trim() || \"unknown\"})" = true := by
  native_decide

end Regex
end Legitimacy
