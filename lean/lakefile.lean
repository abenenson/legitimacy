/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Lake
open Lake DSL

package legitimacy where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Mathlib is pinned to the commit resolved for Lean 4.29.1 so builds do not
-- depend on mutable tag resolution.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

require «channel-capacity» from git
  "https://github.com/abenenson/channel-capacity.git" @ "fdb4d1d18dba3e408fbe1969e09a4da3da2e313e"

require «compact-spectral» from git
  "https://github.com/abenenson/compact-spectral.git" @ "72cd62dbdd4c397d26fc0c5777d60fea2211e938"

require «godel-loeb» from git
  "https://github.com/abenenson/godel-loeb" @ "60a7a1098c34dbd0ee0833dde94ef5315f22d472"

def corpusTheoremWitnessFiles (pkg : NPackage __name__) : Array System.FilePath :=
  let corpusRoot := pkg.dir / ".." / "audits" / "corpus"
  #[
    corpusRoot / "autogen" / "theorem" / "PythonHookCoreProgram.lean",
    corpusRoot / "claude-agent-sdk-python" / "theorem" / "PythonHookCoreProgram.lean",
    corpusRoot / "crewai" / "theorem" / "PythonHookCoreProgram.lean",
    corpusRoot / "langgraph" / "theorem" / "PythonHookCoreProgram.lean",
    corpusRoot / "nemo-guardrails" / "theorem" / "PythonHookCoreProgram.lean"
  ]

def corpusTheoremForbiddenPatterns : Array String :=
  #[
    "^[[:space:]]*(sorry|admit)\\b|^[[:space:]]*axiom[[:space:]]+[A-Za-z_][A-Za-z0-9_']*([[:space:]]*(:|\\(|\\{|\\[)|$)",
    ":=[[:space:]]*(by[[:space:]]+)?(sorry|admit)\\b"
  ]

@[default_target]
lean_lib Legitimacy where
  srcDir := "."

/-- Focused paper-lineage target for direct work on the concrete Stackelberg
node-removal behavioral realization. The root `import Legitimacy` facade now
reaches this module through the behavioral composition surface; this target is
kept as a smaller build entry point for that lineage. -/
lean_lib StackelbergLineage where
  roots := #[`Legitimacy.Behavioral.StackelbergLineage]

@[default_target]
target corpus_theorem_witnesses pkg : Unit := do
  let lean ← getLean
  let leanPath ← getAugmentedLeanPath
  let some legitimacyLib ← findLeanLib? `Legitimacy
    | error "Legitimacy library target not found"
  let legitimacyJob ← legitimacyLib.fetch
  let corpusJob ← legitimacyJob.mapM fun _ => do
    updateAction .build
    for file in corpusTheoremWitnessFiles pkg do
      for pattern in corpusTheoremForbiddenPatterns do
        let out ← rawProc (quiet := true) {
          cmd := "rg"
          args := #["-n", pattern, toString file]
          cwd := pkg.dir
        }
        if out.exitCode = 0 then
          error s!"forbidden corpus theorem witness term found:\n{out.stdout.trimAscii}"
        else if out.exitCode ≠ 1 then
          error s!"corpus theorem witness scan failed with exit code {out.exitCode}"
      proc {
        cmd := lean.toString
        args := #[toString file]
        cwd := pkg.dir
        env := #[("LEAN_PATH", leanPath.toString)]
      }
  return corpusJob.setCaption "corpus theorem witnesses"

/-- Executable fixture roots are not re-exported by `import Legitimacy`; they
exist to materialize byte-stable fixture data for parity checks. -/
lean_exe spectral_fixture_export where
  root := `Legitimacy.Fixtures.ExportSpectral

/-- Executable fixture roots are not re-exported by `import Legitimacy`; they
exist to materialize byte-stable fixture data for parity checks. -/
lean_exe asi_parity_fixture_export where
  root := `Legitimacy.Fixtures.ExportAsiParity

/-- Named RustHookCore fixture target. It is intentionally opt-in because the
module models a concrete extractor fixture rather than a paper-facing theorem
facade export. -/
lean_lib RustHookCoreCodexHooksFixture where
  roots := #[`Legitimacy.Extract.RustHookCore.Fixtures.CodexHooks]
