/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Server
public import Std.Http.Data

public section

namespace Routing

open Std.Http (Method)

/-- A route, or a group of entries mounted under a literal root. -/
inductive Entry where
  | route (route : Route Result)
  | mount (root : MountPoint) (entries : List Entry)

def Entry.get (segs : List PathSeg) (handler : HandlerType segs Result) : Entry :=
  .route (.get segs handler)

def Entry.post (segs : List PathSeg) (handler : HandlerType segs Result) : Entry :=
  .route (.post segs handler)

def Entry.put (segs : List PathSeg) (handler : HandlerType segs Result) : Entry :=
  .route (.put segs handler)

def Entry.delete (segs : List PathSeg) (handler : HandlerType segs Result) : Entry :=
  .route (.delete segs handler)

def Route.prependLits : (pre : List String) → pre.all (!dotSegment ·) → Route result →
    Route result
  | [], _, r => r
  | s :: rest, h, r =>
    have h : dotSegment s = false ∧ rest.all (!dotSegment ·) := by
      simpa only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] using h
    let r := Route.prependLits rest h.2 r
    { method := r.method, segs := .lit s h.1 :: r.segs, handler := r.handler }

def Route.asDirectory : Route result → Route result
  | { method, segs := [], handler } => { method, segs := [.lit ""], handler }
  | r => r

def Route.under (root : MountPoint) (r : Route result) : Route result :=
  if root.segs.isEmpty then r else Route.prependLits root.segs root.valid r.asDirectory

mutual
def Entry.toRoutes : Entry → List (Route Result)
  | .route r => [r]
  | .mount root entries => (Entry.listToRoutes entries).map (Route.under root)

def Entry.listToRoutes : List Entry → List (Route Result)
  | [] => []
  | e :: es => e.toRoutes ++ Entry.listToRoutes es
end

/-- A group of routes behind its own middleware, applied in list order, the first outermost. -/
structure Router where
  middlewares : List (StatelessHandler → StatelessHandler) := []
  routes : List Entry := []
  routers : List Router := []
  fallback : Option StatelessHandler := none

private structure Compiled where
  takes : Method → List String → Bool
  onContinue : LeanIn.Http.H1.Head → Bool
  handler : StatelessHandler

mutual
private def Router.compile : Router → Compiled
  | { middlewares, routes, routers, fallback } =>
    let flat := Entry.listToRoutes routes
    let roots := routes.filterMap fun
      | .mount root _ => some root.segs
      | .route _ => none
    let subs := Router.compileAll routers
    let fallback : StatelessHandler := fallback.getD (Handler.ofFn (fun r => Response.notFound.text "Not Found"))
    let own (method : Method) (path : List String) : Bool :=
      (matchTable flat method path).isSome || wantsSlash flat method path
    let next (method : Method) (path : List String) : StatelessHandler :=
      match subs.find? (·.takes method path) with
      | some sub => sub.handler
      | none => fallback
    let inner : StatelessHandler :=
      { onRequest := fun request =>
          match respond? flat request with
          | some response => response request
          | none => (next request.method (decodedPath request.uri)) request
        onContinue := fun head =>
          let path := match Std.Http.RequestTarget.parse? head.targetString with
            | some target => decodedPath target
            | none => []
          match Std.Http.Method.ofString? head.methodTokenString with
          | none => false
          | some method =>
            if own method path then true else (next method path).onContinue head }
    { takes := fun method path =>
        own method path || roots.any (·.isPrefixOf path) || subs.any (·.takes method path)
      onContinue := fun head => inner.onContinue head
      handler := middlewares.foldr (· ·) inner }

private def Router.compileAll : List Router → List Compiled
  | [] => []
  | r :: rs => r.compile :: Router.compileAll rs
end

def Router.toHandler (router : Router) : StatelessHandler :=
  router.compile.handler

def Router.toStreamHandler (router : Router) : LeanIn.Http.Server.StreamHandler :=
  Routing.toStreamHandlerOf router.toHandler

end Routing
