/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

/-- The LeanIn engine. LeanIn is required here rather than from `routing`, so that an application
serving on `Std.Http.Server` resolves neither it nor the libuv it links against. -/
package «routing-leanin» where
  -- Kept in step with `routing`; see the note in the root lakefile.
  version := v!"0.13.0"

require routing from ".."

-- `main`, for `LeanIn.Http.StdHandler`, which no release carries yet.
require leanin from git
  "https://github.com/scidonia/leanin.git" @ "ffe3a0af70d4dee440ac1a61e23398276a5392b6"

@[default_target]
lean_lib RoutingLeanIn
