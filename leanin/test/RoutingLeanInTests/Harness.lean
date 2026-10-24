/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RoutingStd
import RoutingLeanIn

/-!
Running a handler on either engine in memory, without a socket, and reading back what it answered
in a form both share.
-/

namespace RoutingLeanInTests

open Routing
open Std.Http

structure Outcome where
  status : Status
  headers : Headers
  body : ByteArray

def Outcome.header? (o : Outcome) (name : String) : Option String :=
  (Header.Name.ofString? name).bind fun n => (o.headers.get? n).map toString

def headOf (method : Method) (target : String) : IO Request.Head :=
  match RequestTarget.parse? target with
  | some uri => pure { method, version := .v11, uri }
  | none => throw (IO.userError s!"test target {target.quote} is not a valid request target")

def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- A response body's bytes, refusing one with more chunks than any test here sends. -/
def drainStd (body : Body.Any) : Std.Async.Async ByteArray :=
  go 1000 .empty
where
  go : Nat → ByteArray → Std.Async.Async ByteArray
    | 0, _ => throw (.userError "the response body did not end")
    | fuel + 1, acc => do
      match ← body.recv with
      | some chunk => go fuel (acc ++ chunk.data)
      | none => pure acc

/-- `body` in pieces of at most `piece` bytes. -/
def piecesOf (body : ByteArray) (piece : Nat := 65536) : List ByteArray :=
  (List.range ((body.size + piece - 1) / piece)).map fun i =>
    body.extract (i * piece) ((i + 1) * piece)

/-- A request body arriving as `piecesOf` it, each piece its own read, as a client sending a large
one would. -/
def stdBodyOf (body : ByteArray) : Std.Async.Async Body.Stream :=
  Body.stream fun s => do
    for piece in piecesOf body do
      s.send (Chunk.ofByteArray piece)

def runStd (h : StatelessHandler .std) (method : Method) (target : String)
    (body : ByteArray := .empty) : IO Outcome := do
  let line ← headOf method target
  Std.Async.Async.block <| Std.Async.ContextAsync.run do
    let response ← h.onRequest { line, body := ← stdBodyOf body }
    return { status := response.line.status, headers := response.line.headers
             body := ← drainStd response.body }

def continuesStd (h : StatelessHandler .std) (target : String) : IO Bool := do
  Std.Async.Async.block <| h.onContinue (← headOf .post target)

def runVM (m : LeanIn.Runtime.VM α) : IO α := do
  let cell ← LeanIn.Runtime.RawCell.new
  LeanIn.Runtime.VM.runToCell m cell
  let out ← IO.mkRef none
  LeanIn.Runtime.RawCell.await cell (fun v => out.set (some v))
  match ← out.get with
  | some v => pure v
  | none => throw (IO.userError "the VM suspended, which no handler here should")

/-- A reader handing out `body` in pieces no larger than each `recv` asks for, as LeanIn's driver
does. -/
def readerOf (body : ByteArray) (peer : Option Std.Net.SocketAddress := none) :
    IO LeanIn.Http.Server.BodyReader := do
  let rest ← IO.mkRef body
  return { recv := fun n => (rest.modifyGet fun r =>
             if r.isEmpty then (none, r)
             else
               let k := min (max n 1) r.size
               (some (r.extract 0 k), r.extract k r.size) : IO _)
           drained := ((·.isEmpty) <$> rest.get : IO _)
           leftover := pure .empty
           peer }

def bytesOf : LeanIn.Http.ResponseBody → LeanIn.Runtime.VM ByteArray
  | .bytes data => pure data
  | .stream _ write => do
    let acc ← (IO.mkRef ByteArray.empty : IO _)
    write fun chunk => (acc.modify (· ++ chunk) : IO Unit)
    (acc.get : IO _)

/-- Through `toLeanIn`, so what is run is what LeanIn would serve. -/
def runLeanIn (h : StatelessHandler .leanin) (method : Method) (target : String)
    (body : ByteArray := .empty) : IO Outcome := do
  let line ← headOf method target
  let body ← readerOf body
  runVM do
    let response ← h.toLeanIn.onRequest { line, body }
    return { status := response.line.status, headers := response.line.headers
             body := ← bytesOf response.body }

def continuesLeanIn (h : StatelessHandler .leanin) (target : String) : IO Bool := do
  let head ← headOf .post target
  runVM (h.toLeanIn.onContinue head)

end RoutingLeanInTests
