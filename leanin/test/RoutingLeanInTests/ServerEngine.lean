/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RoutingLeanInTests.Harness

/-!
A router and two middlewares written once over `{e : Engine} [ServerEngine e]`, as a library
generic over the server writes them, answer alike on both engines. Between them they read a
bounded form body and hand on a replacement, call into `IO`, recover from a thrown error through
`onFailure`, and answer with HTML and with nothing.
-/

namespace RoutingLeanInTests.ServerEngine

open Routing
open Routing.ServerEngine
open Std.Http

/-- The body a middleware read, kept for what it hands the request on to. -/
private structure FormBytes where
  bytes : ByteArray
deriving TypeName

private def limit : Nat := 1024

/-- What lean-middleware's `params` does: reads the body, keeps it, and hands on a replacement so
the handler can read it again. A body over `limit` is refused before anything inside runs. -/
private def withFormBytes {e : Engine} [ServerEngine e] (h : StatelessHandler e) :
    StatelessHandler e :=
  { h with onRequest := fun request => do
      let bytes? ← try some <$> readBody request.body limit catch _ => pure none
      match bytes? with
      | none => e.text (Response.withStatus .payloadTooLarge) "Payload Too Large"
      | some bytes =>
        h.onRequest { request with
          body := ← replaceBody request.body bytes
          extensions := request.extensions.insert (FormBytes.mk bytes) } }

private def catchAll {e : Engine} [ServerEngine e] (h : StatelessHandler e) : StatelessHandler e :=
  { h with onRequest := fun request => do
      try h.onRequest request
      catch err => do
        monadLift (h.onFailure err)
        e.text Response.internalServerError "Internal Server Error" }

/-- `name=…` from a form body; enough form parsing for a test of reading one. -/
private def nameOf (form : String) : String :=
  (form.splitOn "&").findSome? (fun field => (field.dropPrefix? "name=").map (·.toString)) |>.getD ""

private def router {e : Engine} [ServerEngine e] (visits : IO.Ref Nat) : Router e :=
  { routes :=
      [ .post [.lit "greet"] fun request => do
          let form ← readText request.body limit
          let kept := (request.extensions.get FormBytes).map (·.bytes)
          let n ← monadLift (visits.modifyGet fun n => (n + 1, n + 1) : IO Nat)
          html Response.ok
            s!"<p>Hello, {nameOf form}, visit {n}, body kept {kept == some form.toUTF8}</p>",
        .get [.lit "boom"] fun _ => throw (.userError "boom"),
        .get [.lit "gone"] fun _ => empty (Response.withStatus .noContent) ] }

private def app {e : Engine} [ServerEngine e] (failures : IO.Ref (List String))
    (inner : StatelessHandler e) : StatelessHandler e :=
  catchAll <| withFormBytes
    { inner with onFailure := fun err => monadLift (failures.modify (· ++ [toString err]) : IO Unit) }

private def bothEngines : IO (List (String × IO.Ref Nat × IO.Ref (List String) ×
    (Method → String → ByteArray → IO Outcome))) := do
  let (stdVisits, stdFailures) := (← IO.mkRef 0, ← IO.mkRef [])
  let (leaninVisits, leaninFailures) := (← IO.mkRef 0, ← IO.mkRef [])
  let std := app stdFailures (router stdVisits).toHandler
  let leanin := app leaninFailures (router leaninVisits).toHandler
  return [ ("std", stdVisits, stdFailures, fun m t b => runStd std m t b),
           ("leanin", leaninVisits, leaninFailures, fun m t b => runLeanIn leanin m t b) ]

#eval show IO Unit from do
  for (engine, visits, failures, run) in ← bothEngines do
    let o ← run .post "/greet" "name=Ada&lang=en".toUTF8
    check s!"{engine}: a form post should be read, kept and greeted, got {repr o.status} \
        {String.fromUTF8? o.body}"
      (o.status == .ok && o.body == "<p>Hello, Ada, visit 1, body kept true</p>".toUTF8 &&
        o.header? "content-type" == some "text/html; charset=utf-8")

    let o ← run .post "/greet" (ByteArray.mk (Array.replicate (limit + 1) 0x61))
    check s!"{engine}: a body over the limit should be refused, got {repr o.status}"
      (o.status == .payloadTooLarge)
    check s!"{engine}: a refused body should not reach the handler" ((← visits.get) == 1)

    let o ← run .get "/boom" .empty
    check s!"{engine}: a thrown error should answer 500, got {repr o.status}"
      (o.status == .internalServerError && o.body == "Internal Server Error".toUTF8)
    let reported ← failures.get
    check s!"{engine}: onFailure should be told of the error once, got {reported}"
      (reported == ["boom"])

    let o ← run .get "/gone" .empty
    check s!"{engine}: an empty response should have no body, got {repr o.status} {o.body.size}"
      (o.status == .noContent && o.body.isEmpty)

-- A replaced LeanIn body keeps the peer address the original carried, and hands its bytes out
-- in the pieces each `recv` asks for.
#eval show IO Unit from do
  let peer : Std.Net.SocketAddress := .v4 { addr := Std.Net.IPv4Addr.ofParts 10 0 0 7, port := 4321 }
  let original ← readerOf .empty (peer := some peer)
  let (replaced, pieces) ← runVM do
    let replaced ← replaceBody (e := .leanin) original "abcde".toUTF8
    let pieces ← [3, 3, 3].mapM fun n => replaced.recv n
    return (replaced, pieces)
  check "the peer address should survive the replacement"
    ((replaced.peer.map toString) == some (toString peer))
  check s!"the bytes should come out in the pieces asked for, got {pieces.map (·.map (·.size))}"
    (pieces == [some "abc".toUTF8, some "de".toUTF8, none])

end RoutingLeanInTests.ServerEngine
