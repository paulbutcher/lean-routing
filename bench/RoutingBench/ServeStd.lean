/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RoutingBench.App
import RoutingStd

open Std Async Http

/-- `benchStd <port>`: the application on `Std.Http.Server`, on loopback. -/
def main (args : List String) : IO UInt32 := do
  let port := (args.head?.bind (·.toNat?)).getD 8601
  let addr : Net.SocketAddress := .v4 { addr := Net.IPv4Addr.ofParts 127 0 0 1, port := port.toUInt16 }
  let handler ← RoutingBench.handler .std
  -- Past the default of 100 requests per connection, so keep-alive survives a run.
  let _ ← Async.toIO (Server.serve addr handler { maxRequests := 1000000000 })
  IO.println s!"benchStd listening on {port}"
  repeat IO.sleep 3600000
  return 0
