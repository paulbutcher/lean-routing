/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

/-- Every shipped package in this repository, this one and each engine's (`std/`, `leanin/`), carries
the same version, and all are bumped together whether or not each one changed: an application
resolves `routing` and an engine together, and one number says which pair it holds. -/
package routing where
  version := v!"0.15.2"

@[default_target]
lean_lib Routing

/-- The tests live in their own package (`test/`) so that nothing they need reaches a
downstream consumer's dependency graph, which means they can only be run as a child process.
`scripts/` holds the two checks that keep the Lean package out of a consumer's binary
(`README.md`); they run here, rather than by hand, so that a plain `import Lean` cannot get
back in unnoticed.

The LeanIn engine's tests are a package of their own (`leanin/test/`): requiring LeanIn links its C
shim into every executable of the requiring package, `test/`'s `leanFree` included. -/
@[test_driver]
script tests do
  let run (cmd : String) (args : Array String) (cwd : System.FilePath) : ScriptM UInt32 := do
    let child ← IO.Process.spawn { cmd, args, cwd }
    child.wait
  let imports ← run (__dir__ / "scripts" / "check-imports.sh").toString #[] __dir__
  if imports != 0 then return imports
  let unit ← run "lake" #["test"] (__dir__ / "test")
  if unit != 0 then return unit
  let leanin ← run "lake" #["test"] (__dir__ / "leanin" / "test")
  if leanin != 0 then return leanin
  run (__dir__ / "scripts" / "check-runtime.sh").toString #[] __dir__
