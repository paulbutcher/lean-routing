/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Shadow
-- So a consumer's module can run the check that `RouteIndex.of`'s default argument evaluates.
public meta import Routing.Shadow
public import Std.Data.HashMap

/-!
`RouteIndex`, a route table with a trie built once over its patterns, so that matching a request
tries only the routes that could match it. `test/RoutingTests/Trie.lean` proves that
`RouteIndex.matchTable` finds the route `matchTable` finds.
-/

public section

@[expose] section

namespace Routing.Internal

open Std.Http (Method)

/-- A segment trie over route patterns. Node `0` is the root. `lits` leads from a node along a
literal segment to its child, and `captures` along a capture of either kind, since
`RouteIndex.matchTable` runs `Route.tryMatch` on each route the trie picks. `routes` holds the indexes
of the routes whose pattern ends at a node. -/
structure Trie where
  lits : Std.HashMap (Nat × String) Nat := {}
  captures : Std.HashMap Nat Nat := {}
  routes : Std.HashMap Nat (List Nat) := {}
  size : Nat := 1

/-- `t` with route `i`, whose pattern continues with `segs` below `node`. -/
def Trie.insert (t : Trie) (i node : Nat) : (segs : List PathSeg) → Trie
  | [] => { t with routes := t.routes.alter node fun is => some (i :: is.getD []) }
  | .lit s _ :: rest =>
    match t.lits[(node, s)]? with
    | some child => t.insert i child rest
    | none =>
      { t with lits := t.lits.insert (node, s) t.size, size := t.size + 1 }.insert i t.size rest
  | .capture _ _ :: rest =>
    match t.captures[node]? with
    | some child => t.insert i child rest
    | none =>
      { t with captures := t.captures.insert node t.size, size := t.size + 1 }.insert i t.size rest

/-- `t` with `routes`, numbered from `i`. -/
def Trie.insertAll (t : Trie) (i : Nat) : List (Route result) → Trie
  | [] => t
  | r :: rs => (t.insert i 0 r.segs).insertAll (i + 1) rs

/-- The routes below `node` whose pattern could match `path`. It includes every one that does,
and may include others. -/
def Trie.candidates (t : Trie) (node : Nat) : (path : List String) → List Nat
  | [] => t.routes.getD node []
  | p :: ps =>
    -- `dispatch` accepts a trailing `""` once a pattern is matched.
    let here := if p == "" && ps.isEmpty then t.routes.getD node [] else []
    let viaLit := match t.lits[(node, p)]? with
      | some child => t.candidates child ps
      | none => []
    let viaCapture := match t.captures[node]? with
      | some child => t.candidates child ps
      | none => []
    here ++ viaLit ++ viaCapture

end Routing.Internal

namespace Routing

open Std.Http (Method)

/-- A route table with a trie over its patterns. Build it once, with `RouteIndex.of`, and match
requests against it with `respond?`. -/
structure RouteIndex (result : Type) where
  routes : Array (Route result)
  trie : Internal.Trie
  /-- The trie is the one `RouteIndex.of` builds, so `RouteIndex.matchTable_eq` covers every index. -/
  trie_eq : trie = ({} : Internal.Trie).insertAll 0 routes.toList
  /-- Every route can be dispatched (`Shadow.lean`). -/
  unshadowed : Internal.unshadowed (routes.toList.map Route.key) = true

/-- `h` is settled while compiling, for a table known then; otherwise use `RouteIndex.ofChecked`. -/
def RouteIndex.of (routes : List (Route result))
    (h : Internal.unshadowed (routes.map Route.key) = true := by routes_unshadowed) :
    RouteIndex result :=
  { routes := routes.toArray, trie := ({} : Internal.Trie).insertAll 0 routes, trie_eq := by simp,
    unshadowed := by simpa using h }

/-- `RouteIndex.of` for a table known only at run time, failing with a line for each route an
earlier one shadows. -/
def RouteIndex.ofChecked (routes : List (Route result)) : Except String (RouteIndex result) :=
  if h : Internal.unshadowed (routes.map Route.key) = true then
    .ok (RouteIndex.of routes h)
  else
    .error (String.intercalate "\n" (Internal.shadowReport (routes.map Route.key)))

/-- The routes that could match `path`, in table order. -/
def RouteIndex.candidates (index : RouteIndex result) (path : List String) : List Nat :=
  (index.trie.candidates 0 path).mergeSort

/-- The first route that matches, as `matchTable` finds it on the table `index` was built from. -/
def RouteIndex.matchTable (index : RouteIndex result) (method : Method) (path : List String) :
    Option (MatchedRoute × result) :=
  (index.candidates path).findSome? fun i => index.routes[i]?.bind (·.tryMatch method path)

end Routing
