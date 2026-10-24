/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RoutingStd
import RoutingLeanIn

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

private structure Outcome where
  status : Status
  body : ByteArray
  route : Option String
  location : Option String

private def outcomeOf (line : Response.Head) (body : ByteArray) : Outcome :=
  { status := line.status, body
    route := (line.headers.get? (.mk "x-route")).map toString
    location := (line.headers.get? Header.Name.location).map toString }

private def targetOf (target : String) : IO RequestTarget :=
  match RequestTarget.parse? target with
  | some uri => pure uri
  | none => throw (IO.userError s!"test target {target.quote} is not a valid request target")

private def headOf (method : Method) (target : String) : IO Request.Head := do
  return { method, version := .v11, uri := ← targetOf target }

section Std

open Std.Async

private partial def drain (body : Body.Any) (acc : ByteArray) : Async ByteArray := do
  match ← body.recv with
  | some chunk => drain body (acc ++ chunk.data)
  | none => pure acc

private def runStd (method : Method) (target : String) : IO Outcome := do
  let line ← headOf method target
  Async.block <| ContextAsync.run do
    let body ← Body.empty
    let response ← (router.toHandler : StatelessHandler .std).onRequest { line, body }
    return outcomeOf response.line (← drain response.body .empty)

private def continuesStd (target : String) : IO Bool := do
  Async.block <| (router.toHandler : StatelessHandler .std).onContinue (← headOf .post target)

end Std

section LeanIn

private def runVM (m : LeanIn.Runtime.VM α) : IO α := do
  let cell ← LeanIn.Runtime.RawCell.new
  LeanIn.Runtime.VM.runToCell m cell
  let out ← IO.mkRef none
  LeanIn.Runtime.RawCell.await cell (fun v => out.set (some v))
  match ← out.get with
  | some v => pure v
  | none => throw (IO.userError "the VM suspended, which no handler here should")

private def emptyBody : LeanIn.Http.Server.BodyReader :=
  { recv := fun _ => pure none, drained := pure true, leftover := pure .empty }

private def bytesOf : LeanIn.Http.ResponseBody → LeanIn.Runtime.VM ByteArray
  | .bytes data => pure data
  | .stream _ write => do
    let acc ← (IO.mkRef ByteArray.empty : IO _)
    write fun chunk => (acc.modify (· ++ chunk) : IO Unit)
    (acc.get : IO _)

private def runLeanIn (method : Method) (target : String) : IO Outcome := do
  let line ← headOf method target
  runVM do
    let response ← (router.toHandler : StatelessHandler .leanin).toLeanIn.onRequest
      { line, body := emptyBody }
    return outcomeOf response.line (← bytesOf response.body)

private def continuesLeanIn (target : String) : IO Bool := do
  let head ← headOf .post target
  runVM ((router.toHandler : StatelessHandler .leanin).toLeanIn.onContinue head)

end LeanIn

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

private def expect (method : Method) (target : String) (status : Status) (body : String)
    (route location : Option String := none) : IO Unit := do
  for (engine, run) in [("std", runStd), ("leanin", runLeanIn)] do
    let o ← run method target
    check s!"{engine} {target}: status {repr o.status}, body {String.fromUTF8? o.body}, \
        route {o.route}, location {o.location}"
      (o.status == status && o.body == body.toUTF8 && o.route == route && o.location == location)

#eval show IO Unit from do
  expect .get "/hello" .ok "hello" (route := some "/hello")
  expect .get "/users/7" .ok "user 7" (route := some "/users/:id")
  expect .get "/blog/" .ok "blog" (route := some "/blog/")
  expect .get "/blog?page=2" .permanentRedirect "" (location := some "/blog/?page=2")
  expect .get "/nope" .notFound "Not Found"
  expect .post "/upload" .ok "up" (route := some "/upload")

  -- The sub-router that would serve `/upload` decides its continue, on either engine.
  for (engine, continues) in [("std", continuesStd), ("leanin", continuesLeanIn)] do
    check s!"{engine}: /upload should refuse its continue" !(← continues "/upload")
    check s!"{engine}: /hello should accept its continue" (← continues "/hello")

end RoutingLeanInTests
