import Routing.Server

/-!
`dispatchBench` separates request-target parsing, route matching and handler execution from the
server stack. Every value printed is nanoseconds per operation on this run; no baseline is implied.
-/

open Routing
open Std.Http

private def routeFor (_ : Nat) : Route Result :=
  .get [.lit "r", .lit "x"] (handler := fun _ => pure (Response.ok.text "ok"))

private def routes : List (Route Result) := (List.range 64).map routeFor

private def requestFor (target : String) : IO Request := do
  let raw := s!"GET {target} HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8
  let head ← match LeanIn.Http.H1.parseHead raw 0 {} with
    | .ok h _ => pure h
    | _ => throw (IO.userError "bad head")
  let line ← match LeanIn.Http.StdHandler.headToStock head with
    | .ok line => pure line
    | .error e => throw e
  let body : LeanIn.Http.Server.BodyReader :=
    { recv := fun _ => pure none, drained := pure true, leftover := pure .empty }
  return { line, body }

private def nsPer (n : Nat) (act : IO Unit) : IO Nat := do
  let t0 ← IO.monoNanosNow
  act
  let t1 ← IO.monoNanosNow
  return (t1 - t0) / n

def main : IO UInt32 := do
  let target := "/r/x"
  let n := 200000
  let parseNs ← nsPer n do
    let mut sink := 0
    for _ in List.range n do
      if (RequestTarget.parse? target).isSome then sink := sink + 1
    unless sink == n do throw (IO.userError "parse sink")
  let matchNs ← nsPer n do
    let mut sink := 0
    for _ in List.range n do
      if ((matchTable routes .get ["r", "x"]).isSome) then sink := sink + 1
    unless sink == n do throw (IO.userError "match sink")
  let request ← requestFor target
  let n2 := 50000
  let runNs ← nsPer n2 do
    for _ in List.range n2 do
      LeanIn.Runtime.VM.run (runRequest routes request >>= fun _ => pure ())
  IO.println s!"dispatch|n={n}|parseNs={parseNs}|matchNs={matchNs}|runNs={runNs}"
  return 0
