/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Server
import Routing.RouteMount

/-!
The real `toHandler` path is exercised through `run` on a LeanIn request: the matched route is
published on the request and the response, a 404 carries neither, and a mounted index redirects
with the query intact.
-/

namespace Routing

open Std.Http

private structure SeenByHandler where
  matched : Option MatchedRoute
deriving TypeName

private def userSegs : List PathSeg := [.lit "users", .capture "id" .nat]

private def serverRoutes : List (Route Result) :=
  [ .get userSegs (handler := fun (id : Nat) request => do
      let response := Response.ok.text s!"user #{id}"
      return { response with
        extensions := response.extensions.insert
          (SeenByHandler.mk (matchedRoute? request.extensions)) }) ]


private def runVM (m : LeanIn.Runtime.VM α) : IO α := do
  let cell ← LeanIn.Runtime.RawCell.new (α := α)
  LeanIn.Runtime.VM.runToCell m cell
  let out ← IO.mkRef (none : Option α)
  LeanIn.Runtime.RawCell.await cell (fun v => out.set (some v))
  match ← out.get with
  | some v => pure v
  | none => throw (IO.userError "test VM suspended; this test expects a pure response")

private def emptyBody : LeanIn.Http.Server.BodyReader :=
  { recv := fun _ => pure none, drained := pure true, leftover := pure .empty }

private def requestFor (methodName target : String) : IO Request := do
  let raw := s!"{methodName} {target} HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8
  let head ← match LeanIn.Http.H1.parseHead raw 0 {} with
    | .ok head _ => pure head
    | .failed _ => throw (IO.userError s!"could not parse {target.quote}")
    | .incomplete => throw (IO.userError s!"incomplete request {target.quote}")
  let line ← match LeanIn.Http.StdHandler.headToStock head with
    | .ok line => pure line
    | .error e => throw e
  return { line, body := emptyBody }

private def runRoutes (routes : List (Route Result)) (methodName target : String) : IO Response := do
  let request ← requestFor methodName target
  runVM (Routing.runRequest routes request Routing.defaultNotFound)

private def runOne (methodName target : String) : IO Response :=
  runRoutes serverRoutes methodName target

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"{label}")

#eval show IO Unit from do
  let response ← runOne "GET" "/users/7"
  let expected : MatchedRoute := { method := .get, segs := userSegs }
  check s!"response should carry {repr expected}, got {repr (matchedRoute? response.extensions)}"
    (matchedRoute? response.extensions == some expected)
  check s!"response body, got {String.fromUTF8? response.body}"
    (response.body == "user #7".toUTF8)
  let seen := response.extensions.get SeenByHandler
  check "handler should see the matched route on its request"
    (seen.map (·.matched) == some (some expected))
  check s!"response should carry the endpoint template"
    (matchedPattern? response.extensions == some "/users/:id")

  let response ← runOne "GET" "/nope"
  check "404 response should carry no MatchedRoute" (matchedRoute? response.extensions == none)
  check "404 should carry no template" (matchedPattern? response.extensions == none)
  check "404 status" (response.status == 404)

private def blogOwnRoutes : List (Route Result) :=
  [ .get [] (handler := fun _request => pure ((Response.ok.text "blog"))),
    .post [.lit "posts"] (handler := fun _request => pure ((Response.ok.text "posted"))) ]

private def blogRoutes : List (Route Result) := mount_routes "/blog" blogOwnRoutes

#eval show IO Unit from do
  let response ← runRoutes blogRoutes "GET" "/blog?x=1"
  check s!"mounted index should redirect, got {response.status}" (response.status == 308)
  let location := response.headers.findSome? fun (n, v) => if n == "location" then some v else none
  check s!"redirect should keep the query, got {repr location}" (location == some "/blog/?x=1")


end Routing
