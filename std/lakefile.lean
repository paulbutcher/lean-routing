/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

/-- The `Std.Http.Server` engine. It requires nothing beyond `routing`, so an application serving
on `Std.Http.Server` resolves neither LeanIn nor libuv. -/
package «routing-std» where
  -- Kept in step with `routing`; see the note in the root lakefile.
  version := v!"0.13.1"

require routing from ".."

@[default_target]
lean_lib RoutingStd
