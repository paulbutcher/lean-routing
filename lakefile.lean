/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package routing where
  version := v!"0.5.0"

@[default_target]
lean_lib Routing

/-- The tests live in their own package (`test/`) so that nothing they need reaches a
downstream consumer's dependency graph, which means they can only be run as a child process. -/
@[test_driver]
script tests do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait
