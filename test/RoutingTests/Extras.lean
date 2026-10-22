import Routing.Streaming
import Extras.Json

namespace RoutingTests.Extras

open Routing

structure Todo where
  title : String
  done : Bool := false
deriving Lean.ToJson
open Std.Http

private def requestFor (target : String) : IO Request := do
  let some method := Method.ofString? "GET"
    | throw (IO.userError "bad method")
  let some uri := RequestTarget.parse? target
    | throw (IO.userError "bad target")
  let raw := s!"GET {target} HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8
  let head ← match LeanIn.Http.H1.parseHead raw 0 {} with
    | .ok head _ => pure head
    | _ => throw (IO.userError "bad head")
  let body : LeanIn.Http.Server.BodyReader :=
    { recv := fun _ => pure none, drained := pure true, leftover := pure .empty }
  return { head, uri, method, body }

private structure Captured where
  status : Option Nat := none
  body : ByteArray := .empty

private def runVM (m : LeanIn.Runtime.VM α) : IO α := do
  let cell ← LeanIn.Runtime.RawCell.new (α := α)
  LeanIn.Runtime.VM.runToCell m cell
  let out ← IO.mkRef (none : Option α)
  LeanIn.Runtime.RawCell.await cell (fun v => out.set (some v))
  match ← out.get with
  | some v => pure v
  | none => throw (IO.userError "test VM suspended")

private def setStatus (r : IO.Ref Captured) (n : Nat) : LeanIn.Runtime.VM Unit :=
  monadLift (BaseIO.toIO (r.modify fun c => { c with status := some n }) : IO Unit)

private def appendBody (r : IO.Ref Captured) (bs : ByteArray) : LeanIn.Runtime.VM Unit :=
  monadLift (BaseIO.toIO (r.modify fun c => { c with body := c.body ++ bs }) : IO Unit)

#eval show IO Unit from do
  let captured ← IO.mkRef ({} : Captured)
  let writer : LeanIn.Http.Server.ResponseWriter :=
    { sendContinue := pure ()
      interim := fun _ => pure ()
      start := fun (rh : LeanIn.Http.H1.ResponseHead) => setStatus captured rh.status
      write := fun (bs : ByteArray) => appendBody captured bs
      finish := pure ()
      status := pure (true, true, false)
      code := pure (some 200) }
  let route : Route Streaming.Result :=
    .get [.lit "stream"] fun _ w => do
      w.start { status := 200, reason := "OK" }
      w.write "hello ".toUTF8
      w.write "stream".toUTF8
      w.finish
  let request ← requestFor "/stream"
  let some action := Streaming.respond? (RouteIndex.of [route]) request writer
    | throw (IO.userError "streaming route did not match")
  runVM action
  let got ← captured.get
  unless got.status == some 200 && got.body == "hello stream".toUTF8 do
    throw (IO.userError s!"streaming response mismatch: status={got.status}")

  let response := (Response.ok.json ({ title := "x", done := true } : RoutingTests.Extras.Todo))
  unless response.body == "{\"done\":true,\"title\":\"x\"}".toUTF8 do
    throw (IO.userError s!"json body mismatch: {String.fromUTF8? response.body}")
  let ctype := response.headers.findSome? fun (n, v) => if n == "content-type" then some v else none
  unless ctype == some "application/json" do
    throw (IO.userError s!"json content type mismatch: {repr ctype}")

end RoutingTests.Extras
