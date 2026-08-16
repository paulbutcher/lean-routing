/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Routing.Route

/-!
`mount_routes "prefix" routes`: the `Route`-level analogue of `route_table`'s `mount` row
(`RouteTable.lean`). It prefixes every route in `routes` (a `List (Route result)`, typically built
against a sub-app's own, unprefixed `route_table`-generated `patterns`) with `prefix`'s literal
segments, for splicing into a parent app's route list.

Unlike `mount`, this needs no structural recursion to reach arbitrary nesting depth: `Route`s
already live in a flat, ordered `List`, so nesting is just repeated prefixing and `++`, which
associates freely (`mount_routes "/outer" (mount_routes "/mid" innerRoutes ++ ownRoutes)`).

No handler-level glue is needed either: `HandlerType` (`Handler.lean`) skips over `.lit` segments
without adding an argument, so a handler built against the sub-app's own unprefixed pattern already
has exactly the type needed once prefixed; only each route's `segs` field actually changes.
Lean accepts the unchanged `handler` field by straight reduction: the prefix's `.lit` segments are
literal constructors sitting right there in the generated term (not hidden behind an opaque
variable), so `HandlerType (prefix ++ segs) result` reduces to `HandlerType segs result` for any
`segs`, without a cast or proof.
-/

namespace Routing

open Lean

private def segTerm : PathSeg → MacroM (TSyntax `term)
  | .lit s => `(Routing.PathSeg.lit $(quote s))
  | .capture name .nat => `(Routing.PathSeg.capture $(quote name) .nat)
  | .capture name .string => `(Routing.PathSeg.capture $(quote name) .string)

/-- Parses `pat` into segments for a mount prefix, rejecting captures: the same restriction, and
the same error message, as `route_table`'s `mount` row; see `prefixSegsSrcFor`,
`RouteTable.lean`. -/
private def mountPrefixSegs (pat : TSyntax `str) : MacroM (List PathSeg) := do
  match parsePattern pat.getString with
  | none => Macro.throwErrorAt pat s!"invalid route pattern {pat.getString.quote}"
  | some segs =>
      if segs.any (fun | .capture .. => true | .lit _ => false) then
        Macro.throwErrorAt pat
          s!"mount prefix must not contain captures (got {pat.getString.quote}); captured mount prefixes are not yet supported"
      else
        pure segs

macro "mount_routes" pat:str routes:term:max : term => do
  let segs ← mountPrefixSegs pat
  let segTerms ← segs.toArray.mapM segTerm
  `(($routes).map fun r => { r with segs := [$segTerms,*] ++ r.segs })

end Routing
