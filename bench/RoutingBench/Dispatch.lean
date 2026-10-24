/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RoutingBench.App
import RoutingStd
import RoutingLeanIn

/-!
`benchDispatch [iterations]`: the application's handler run in memory, without a socket, on each
engine, for each of `RoutingBench.targets`. `match` is dispatch alone, with no engine; the gap
between it and an engine's figure is that engine's cost of running a handler and building its
response. Every figure is nanoseconds per request on this run.

Each iteration reads its request head from an `IO.Ref`, and folds what it got back into a sum that
is checked. Without both, the compiler may drop a pure match whose result is unused, and LeanIn's
`VM` runs a computation with no effects while it is being built, before the clock starts. The
read is in every figure, `match`'s included.
-/

open Routing
open Std.Http

def requestHead (target : String) : IO Request.Head :=
  match RequestTarget.parse? target with
  | some uri => pure { method := .get, version := .v11, uri }
  | none => throw (IO.userError s!"{target.quote} is not a request target")

def nsPer (n : Nat) (act : IO Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let sink ← act
  let t1 ← IO.monoNanosNow
  if sink == 0 then throw (IO.userError "nothing was dispatched")
  return (t1 - t0) / n

def matchOnly (n : Nat) (head : IO.Ref Request.Head) : IO Nat := do
  let index ← IO.ofExcept (RouteIndex.ofChecked (Entry.listToRoutes (RoutingBench.router (e := .std)).routes))
  nsPer n do
    let mut sink := 0
    for _ in List.range n do
      let head ← head.get
      sink := sink + match index.matchTable head.method (decodedPath head.uri) with
        | some (matched, _) => matched.segs.length + 1
        | none => 1
    return sink

def onStd (n : Nat) (head : IO.Ref Request.Head) : IO Nat := do
  let h ← RoutingBench.handler .std
  nsPer n <| Std.Async.Async.block <| Std.Async.ContextAsync.run do
    let mut sink := 0
    for _ in List.range n do
      let line ← head.get
      let body ← Body.empty
      let response ← h.onRequest { line, body }
      sink := sink + response.line.status.toCode.toNat
    return sink

def runVM (m : LeanIn.Runtime.VM α) : IO α := do
  let cell ← LeanIn.Runtime.RawCell.new
  LeanIn.Runtime.VM.runToCell m cell
  let out ← IO.mkRef none
  LeanIn.Runtime.RawCell.await cell (fun v => out.set (some v))
  match ← out.get with
  | some v => pure v
  | none => throw (IO.userError "the VM suspended, which no handler here should")

def onLeanIn (n : Nat) (head : IO.Ref Request.Head) : IO Nat := do
  let h ← RoutingBench.handler .leanin
  let body : LeanIn.Http.Server.BodyReader :=
    { recv := fun _ => pure none, drained := pure true, leftover := pure .empty }
  nsPer n <| runVM do
    let mut sink := 0
    for _ in List.range n do
      let line ← (head.get : IO _)
      let response ← h.onRequest { line, body }
      sink := sink + response.line.status.toCode.toNat
    return sink

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind (·.toNat?)).getD 100000
  IO.println "target|exercises|matchNs|stdNs|leaninNs"
  for (target, what) in RoutingBench.targets do
    let head ← IO.mkRef (← requestHead target)
    IO.println s!"{target}|{what}|{← matchOnly n head}|{← onStd n head}|{← onLeanIn n head}"
  return 0
