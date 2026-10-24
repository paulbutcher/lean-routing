/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

/-- The two engines serving one application, for `run.sh` to compare. Not shipped: nothing requires
this package. -/
package «routing-bench»

require «routing-std» from "../std"

require «routing-leanin» from "../leanin"

lean_lib RoutingBench where
  globs := #[.submodules `RoutingBench]

-- LeanIn's shim is linked into every executable here; libuv, which it wraps, is a system library.
def uvLinkArgs : Array String := #["-luv"]

@[default_target]
lean_exe benchStd where
  root := `RoutingBench.ServeStd
  moreLinkArgs := uvLinkArgs

@[default_target]
lean_exe benchLeanIn where
  root := `RoutingBench.ServeLeanIn
  moreLinkArgs := uvLinkArgs

@[default_target]
lean_exe benchDispatch where
  root := `RoutingBench.Dispatch
  moreLinkArgs := uvLinkArgs
