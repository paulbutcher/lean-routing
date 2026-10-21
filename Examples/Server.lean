import Routing.Server
import LeanIn.Http.Server
import LeanIn.Runtime.Net

/-!
`routingServer <port>` — the routing library on LeanIn's HTTP/1.1 server.

The routes are deliberately small: `/bench` for the paired throughput shape, `/users/:id` for a
typed capture, and a mounted `/blog` index for the redirect. All responses are buffered.
-/

open Routing
open Std.Http

private def benchSegs : List PathSeg := [.lit "bench"]
private def userSegs : List PathSeg := [.lit "users", .capture "id" .nat]
private def blogSegs : List PathSeg := [.lit "blog"]

private def routes : List (Route Result) :=
  [ .get benchSegs (handler := fun _ => pure (Response.ok.text "hello")),
    .get userSegs (handler := fun (id : Nat) _ => pure (Response.ok.text s!"user {id}")),
    .get blogSegs (handler := fun _ => pure (Response.ok.text "blog")) ]

def main (args : List String) : IO UInt32 := do
  let port : UInt16 := ((args.headD "8787").toNat?.getD 8787).toUInt16
  let hooks ← LeanIn.Runtime.Hooks.new
  let l ← LeanIn.Runtime.Listener.bind (LeanIn.Runtime.loopback port)
  let addr ← LeanIn.Runtime.Listener.sockName l
  let e ← LeanIn.Sched.Executor.new LeanIn.Task.Item 256 1
  let cfg : LeanIn.Http.Server.Config := { h1 := { maxMessages := 1000000000 }, clock := LeanIn.Runtime.Clock.live hooks }
  IO.println s!"routing server listening on {addr}"
  let prog : LeanIn.Task.EAsync IO.Error Unit :=
    LeanIn.Runtime.serveForever hooks l
      (LeanIn.Http.Server.serveConnStream cfg · (Routing.toHandler routes))
  let outcome : Except IO.Error Unit ← LeanIn.Runtime.run e prog
  LeanIn.Runtime.Io.stop
  match outcome with
  | .ok _ => return 0
  | .error err => IO.eprintln s!"the accept loop ended: {err}"; return 1
