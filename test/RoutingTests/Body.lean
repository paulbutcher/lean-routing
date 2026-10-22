import Routing.Body

/-!
The body capability on both hosts: the native reader's `readAll` and the stock stream's
capability type-check; the stock response conversion preserves bytes.
-/

namespace RoutingTests.Body

open Std Async
open Routing

private def runVM (m : LeanIn.Runtime.VM α) : IO α := do
  let cell ← LeanIn.Runtime.RawCell.new (α := α)
  LeanIn.Runtime.VM.runToCell m cell
  let out ← IO.mkRef (none : Option α)
  LeanIn.Runtime.RawCell.await cell (fun v => out.set (some v))
  match ← out.get with
  | some v => pure v
  | none => throw (IO.userError "test VM suspended")

private def nativeReader : IO LeanIn.Http.Server.BodyReader := do
  let sent ← IO.mkRef false
  return {
    recv := fun _ => do
      let done ← (monadLift (sent.get : IO Bool) : LeanIn.Runtime.VM Bool)
      if done then pure none else do
        monadLift (sent.set true : IO Unit)
        pure (some "hello".toUTF8)
    drained := pure true
    leftover := pure .empty
  }

/-- The stock body capability is available at the same call shape. -/
def stockRead (body : Std.Http.Body.Stream) : ContextAsync ByteArray :=
  Body.readAll body

#eval show IO Unit from do
  let reader ← nativeReader
  let got ← runVM (Body.readAll (m := LeanIn.Runtime.VM) reader)
  unless got == "hello".toUTF8 do
    throw (IO.userError s!"native body size {got.size}")
  Async.block <| ContextAsync.run do
    let any ← Body.ResponseBody.toStock (body := (Body.ResponseBody.bytes "hello".toUTF8 : Body.ResponseBody ContextAsync))
    let chunk ← Std.Http.Body.recv any
    let got := chunk.map (·.data) |>.getD .empty
    unless got == "hello".toUTF8 do
      throw (IO.userError s!"stock body size {got.size}")

end RoutingTests.Body
