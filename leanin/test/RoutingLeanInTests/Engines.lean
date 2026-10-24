/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RoutingLeanInTests.Harness

/-!
One route table, one middleware and one `Router`, each written once over any engine, answer the
same requests the same way on `Std.Http.Server`'s engine and on LeanIn's.
-/

namespace RoutingLeanInTests

open Routing
open Std.Http

/-- Publishes the matched template as `x-route`, so a response shows which route served it. -/
private def withRouteHeader {e : Engine} (h : StatelessHandler e) : StatelessHandler e :=
  { h with onRequest := fun request => do
      let response ← h.onRequest request
      match (matchedPattern? response.extensions).bind Header.Value.ofString? with
      | some route =>
        return { response with
          line := { response.line with
            headers := response.line.headers.insert (.mk "x-route") route } }
      | none => return response }

private def refuseContinue {e : Engine} (h : StatelessHandler e) : StatelessHandler e :=
  { h with onContinue := fun _ => pure false }

private def ok {e : Engine} (body : String) : Result e := fun _ => e.text Response.ok body

private def router {e : Engine} : Router e :=
  { middlewares := [withRouteHeader]
    routes :=
      [ .get [.lit "hello"] (ok "hello"),
        .get [.lit "users", .capture "id" .nat] fun (id : Nat) => ok s!"user {id}",
        .mount (.mk ["blog"]) [ .get [] (ok "blog") ] ]
    routers := [ { middlewares := [refuseContinue], routes := [ .post [.lit "upload"] (ok "up") ] } ] }

private def stdHandler : StatelessHandler .std := router.toHandler

private def leaninHandler : StatelessHandler .leanin := router.toHandler

private def expect (method : Method) (target : String) (status : Status) (body : String)
    (route location : Option String := none) : IO Unit := do
  for (engine, run) in [("std", runStd stdHandler), ("leanin", runLeanIn leaninHandler)] do
    let o ← run method target
    let (r, l) := (o.header? "x-route", o.header? "location")
    check s!"{engine} {target}: status {repr o.status}, body {String.fromUTF8? o.body}, \
        route {r}, location {l}"
      (o.status == status && o.body == body.toUTF8 && r == route && l == location)

#eval show IO Unit from do
  expect .get "/hello" .ok "hello" (route := some "/hello")
  expect .get "/users/7" .ok "user 7" (route := some "/users/:id")
  expect .get "/blog/" .ok "blog" (route := some "/blog/")
  expect .get "/blog?page=2" .permanentRedirect "" (location := some "/blog/?page=2")
  expect .get "/nope" .notFound "Not Found"
  expect .post "/upload" .ok "up" (route := some "/upload")

  -- The sub-router that would serve `/upload` decides its continue, on either engine.
  for (engine, continues) in
      [("std", continuesStd stdHandler), ("leanin", continuesLeanIn leaninHandler)] do
    check s!"{engine}: /upload should refuse its continue" !(← continues "/upload")
    check s!"{engine}: /hello should accept its continue" (← continues "/hello")

end RoutingLeanInTests
