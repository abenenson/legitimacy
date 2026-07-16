/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Lake
open Lake DSL System

/-!
# Root Lake build facade

The Lean package lives under `lean/`. This root-level facade keeps repository
sentinels that invoke `lake build` from the repository root aligned with the
actual Lean package without duplicating dependency declarations.
-/

package legitimacy_root where

@[default_target]
target lean_subpackage pkg : Unit := do
  Job.async (caption := "lean subpackage build") do
    let traceFile := pkg.buildDir / "lean-subpackage.trace"
    buildUnlessUpToDate traceFile (← getTrace) traceFile do
      proc {
        cmd := "lake"
        args := #["exe", "cache", "get"]
        cwd := pkg.dir / "lean"
      }
      proc {
        cmd := "lake"
        args := #["build"]
        cwd := pkg.dir / "lean"
      }
