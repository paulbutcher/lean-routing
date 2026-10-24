/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RoutingBench.App
import RoutingLeanIn
import LeanIn.Runtime.Multi

open LeanIn LeanIn.Http

/-- `benchLeanIn <port> [carriers]`: the application on LeanIn, on loopback. -/
def main (args : List String) : IO UInt32 := do
  let port := ((args.head?.bind (·.toNat?)).getD 8602).toUInt16
  let carriers := ((args.drop 1).head?.bind (·.toNat?)).getD 1
  let handler := (← RoutingBench.handler .leanin).toLeanIn
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback port)
  let e ← Sched.Executor.new LeanIn.Task.Item 256 carriers
  -- `maxMessages` past the default for the same reason as `benchStd`'s `maxRequests`.
  let cfg : Server.Config :=
    { h1 := { maxMessages := 1000000000 }, clock := Runtime.Clock.live hooks
      continuePolicy := .application }
  IO.println s!"benchLeanIn listening on {port}, {carriers} carrier(s)"
  let (_, outcome) ← Runtime.runCarriersWait e carriers
    (Runtime.serveForeverShared hooks e l fun c => Server.serveConnStd cfg c handler)
  Runtime.Io.stop
  match outcome with
  | .ok _ => return 0
  | .error err =>
    IO.eprintln s!"the accept loop ended: {err}"
    return 1
