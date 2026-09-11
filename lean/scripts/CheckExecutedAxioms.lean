/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Legitimacy.Protocol.ExecutedComposition
import Lean.Util.CollectAxioms

/-! Check every constant owned by the executed-composition module, including private
helpers, proof-valued definitions, opaque proofs, and declarations outside its usual
namespace. Imported dependencies are checked transitively through every owned constant;
new local axioms are rejected outright. Theorem and definition counts remain explicit
so proof coverage is not confused with a hand-maintained list of public headlines. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some target := env.getModuleIdx? `Legitimacy.Protocol.ExecutedComposition
    | throwError "executed composition module was not imported"
  let mut checked := 0
  let mut definitions := 0
  let mut opaques := 0
  let mut constants := 0
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some target then
      constants := constants + 1
      match info with
      | .thmInfo _ =>
        checked := checked + 1
      | .defnInfo _ => definitions := definitions + 1
      | .opaqueInfo _ => opaques := opaques + 1
      | .axiomInfo _ => throwError "executed composition declares an axiom: {name}"
      | _ => pure ()
      -- Inspect all constant kinds: a proof need not be declared as a theorem,
      -- and an imported forbidden axiom need not create a local axiom declaration.
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
  if checked == 0 then
    throwError "executed composition theorem inventory is empty"
  logInfo m!"executed theorem footprints: {checked} module theorems; {definitions} definitions; {opaques} opaque constants; {constants} total owned constants checked; only propext, Classical.choice, Quot.sound"
