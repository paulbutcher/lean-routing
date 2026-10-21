import Routing
import Std.Http.Server

open Std Async
open Std Http Server

private def benchSegs : List Routing.PathSeg := [.lit "bench"]
private def userSegs : List Routing.PathSeg := [.lit "users", .capture "id" .nat]
private def blogSegs : List Routing.PathSeg := [.lit "blog"]

private def routes : List (Routing.Route Routing.Result) :=
  [ .get benchSegs (handler := fun _ => Response.ok.text "hello"),
    .get userSegs (handler := fun (id : Nat) _ => Response.ok.text s!"user {id}"),
    .get blogSegs (handler := fun _ => Response.ok.text "blog") ]

def main (args : List String) : IO UInt32 := do
  let port := (args.headD "8787").toNat?.getD 8787
  let addr : Std.Net.SocketAddress := .v4 { addr := Std.Net.IPv4Addr.ofParts 127 0 0 1, port := port.toUInt16 }
  let handler := Routing.toHandler routes
  let _ ← Async.toIO (Server.serve addr handler { maxRequests := 1000000000 })
  IO.sleep 3600000
  return 0
