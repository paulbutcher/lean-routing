/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Server

public section

namespace Routing

variable {e : Engine}

open Std.Http (Method RequestTarget)

/-- A route, or a group of entries mounted under a literal root. A mount's entries are written
against patterns relative to its root, typically the mounted table's own unprefixed `patterns`. -/
inductive Entry (e : Engine) where
  | route (route : Route (Result e))
  | mount (root : MountPoint) (entries : List (Entry e))

/-- `Route`'s per-method aliases, as entries; a handler's type is still fixed by its pattern. -/
@[expose] def Entry.get (segs : List PathSeg) (handler : HandlerType segs (Result e)) : Entry e :=
  .route (.get segs handler)

@[expose] def Entry.post (segs : List PathSeg) (handler : HandlerType segs (Result e)) : Entry e :=
  .route (.post segs handler)

@[expose] def Entry.put (segs : List PathSeg) (handler : HandlerType segs (Result e)) : Entry e :=
  .route (.put segs handler)

@[expose] def Entry.delete (segs : List PathSeg) (handler : HandlerType segs (Result e)) : Entry e :=
  .route (.delete segs handler)

/-- `r` with the literals `pre` in front. Its handler needs no cast, because `HandlerType` reduces
through a `.lit`. -/
@[expose] def Route.prependLits : (pre : List String) → pre.all (!dotSegment ·) → Route result →
    Route result
  | [], _, r => r
  | s :: rest, h, r =>
    have h : dotSegment s = false ∧ rest.all (!dotSegment ·) := by
      simpa only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] using h
    let r := Route.prependLits rest h.2 r
    { method := r.method, segs := .lit s h.1 :: r.segs, handler := r.handler }

/-- An index as a directory, so it renders and matches with a trailing slash once mounted. -/
@[expose] def Route.asDirectory : Route result → Route result
  | { method, segs := [], handler } => { method, segs := [.lit ""], handler }
  | r => r

/-- `r` under `root`, with the segments `mountSegs` gives. -/
@[expose] def Route.under (root : MountPoint) (r : Route result) : Route result :=
  if root.segs.isEmpty then r else Route.prependLits root.segs root.valid r.asDirectory

mutual
/-- The routes an entry serves, in order, each with the full pattern of every mount enclosing it. -/
@[expose] def Entry.toRoutes : Entry e → List (Route (Result e))
  | .route r => [r]
  | .mount root entries => (Entry.listToRoutes entries).map (Route.under root)

@[expose] def Entry.listToRoutes : List (Entry e) → List (Route (Result e))
  | [] => []
  | entry :: rest => entry.toRoutes ++ Entry.listToRoutes rest
end

/-- A group of routes behind its own middleware, applied in list order, the first outermost.

A router takes a request if one of its routes matches it, or would with a trailing slash, if it
falls under one of its mounts' roots, or if one of its `routers` takes it. It serves a request with
its first route that matches (or the redirect `respond?` gives), else its first sub-router that
takes it, else `fallback`, a plain `404 Not Found` when `none`. So a miss under a mount is answered
by the router holding the mount, behind that router's middleware. -/
structure Router (e : Engine) where
  middlewares : List (StatelessHandler e → StatelessHandler e) := []
  routes : List (Entry e) := []
  routers : List (Router e) := []
  fallback : Option (StatelessHandler e) := none

/-- The roots of the mounts among `entries`, which a router takes every request under. -/
@[expose] def Entry.listRoots (entries : List (Entry e)) : List (List String) :=
  entries.filterMap fun
    | .mount root _ => some root.segs
    | .route _ => none

mutual
/-- What takes a request before the routes after it, in the order a router tries them: its own
routes, then their slash redirects, then each sub-router's takers. Its mount roots come last, since
only a router tried after it never sees what they take. -/
@[expose] def Router.takers : Router e → List Internal.Taker
  | { routes, routers, .. } =>
    let own := Entry.listToRoutes routes
    own.map Route.key ++ own.filterMap Route.redirect? ++ Router.takersOf routers ++
      (Entry.listRoots routes).map .root

@[expose] def Router.takersOf : List (Router e) → List Internal.Taker
  | [] => []
  | r :: rs => r.takers ++ Router.takersOf rs
end

/-- What a router compiles to. `served` is the route its handler answers a request for `target`
with, middleware aside. -/
structure Internal.Compiled (e : Engine) where
  takes : Method → List String → Bool
  served : Method → RequestTarget → Option MatchedRoute
  handler : StatelessHandler e

mutual
/-- Everything not depending on the request is computed here, once, middleware included. -/
def Internal.compile :
    (r : Router e) → Internal.unshadowed r.takers = true → Internal.Compiled e
  | { middlewares, routes, routers, fallback }, h =>
    have h := Internal.unshadowed_append _ _ (by rwa [Router.takers] at h)
    have hs := Internal.unshadowed_append _ _ h.1
    let index := RouteIndex.of (Entry.listToRoutes routes)
      (Internal.unshadowed_append _ _ hs.1).1
    let roots := Entry.listRoots routes
    let subs := Internal.compileAll routers hs.2
    let fallback := fallback.getD (.ofFn defaultNotFound)
    let own (method : Method) (path : List String) : Bool :=
      (index.matchTable method path).isSome || wantsSlash index method path
    let next? (method : Method) (path : List String) : Option (Internal.Compiled e) :=
      subs.find? (·.takes method path)
    let next (method : Method) (path : List String) : StatelessHandler e :=
      match next? method path with
      | some sub => sub.handler
      | none => fallback
    let inner : StatelessHandler e :=
      { onRequest := fun request =>
          match respond? index request with
          | some response => response
          | none => (next request.line.method (decodedPath request.line.uri)).onRequest request
        -- A sub-router's middleware may refuse a body it would not accept, so ask the router
        -- that would serve the request.
        onContinue := fun head =>
          let path := decodedPath head.uri
          if own head.method path then pure true else (next head.method path).onContinue head }
    { takes := fun method path =>
        own method path || roots.any (·.isPrefixOf path) || subs.any (·.takes method path)
      served := fun method target =>
        let path := decodedPath target
        match index.matchTable method path with
        | some (matched, _) => some matched
        | none =>
          if (slashRedirect? index method target path).isSome then none
          else (next? method path).bind (·.served method target)
      handler := middlewares.foldr (· ·) inner }

def Internal.compileAll :
    (rs : List (Router e)) → Internal.unshadowed (Router.takersOf rs) = true →
      List (Internal.Compiled e)
  | [], _ => []
  | r :: rs, h =>
    have h := Internal.unshadowed_append _ _ (by rwa [Router.takersOf] at h)
    Internal.compile r h.1 :: Internal.compileAll rs h.2
end

def Router.toHandler (router : Router e)
    (h : Internal.unshadowed router.takers = true := by routes_unshadowed) :
    StatelessHandler e :=
  (Internal.compile router h).handler

/-- `Router.toHandler` for a router known only at run time, failing as `RouteIndex.ofChecked`
does. -/
def Router.toHandlerChecked (router : Router e) : Except String (StatelessHandler e) :=
  if h : Internal.unshadowed router.takers = true then .ok (router.toHandler h)
  else .error (String.intercalate "\n" (Internal.shadowReport router.takers))

end Routing
