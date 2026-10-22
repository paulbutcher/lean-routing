import Routing.BodyHandler
import Routing.Pilot

/-!
The body-valued result on both hosts: the same handler value is converted to LeanIn's response
and to the stock response, and a static-file handler type-checks at both instantiations.
-/

namespace RoutingTests.BodyHandler

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

def textHandler : BodyHandlerM LeanIn.Runtime.VM LeanIn.Http.Server.BodyReader :=
  { onRequest := fun _ => pure (ResponseM.text "hello") }

def stockTextHandler : BodyHandlerM ContextAsync Std.Http.Body.Stream :=
  { onRequest := fun _ => pure (ResponseM.text "hello") }

def native : LeanIn.Http.Server.StreamHandler := toStreamHandlerBodyOf textHandler

def stock : Std.Http.Server.StatelessHandler := toStockHandlerBodyOf stockTextHandler

def nativeFile : BodyHandlerM LeanIn.Runtime.VM LeanIn.Http.Server.BodyReader :=
  staticFileDeferred "/dev/null"

def stockFile : BodyHandlerM ContextAsync Std.Http.Body.Stream :=
  staticFileDeferred "/dev/null"

def stockFields (request : RequestM Std.Http.Body.Stream) :
    ContextAsync (List (String × String)) :=
  multipartFields request

#eval show IO Unit from do
  let response : ResponseM LeanIn.Runtime.VM := ResponseM.text "hello"
  let native := ResponseM.toLeanIn response
  unless native.line.status == .ok do
    throw (IO.userError "native status")
  let headers := Std.Http.Headers.empty
    |>.insert (Std.Http.Header.Name.ofString! "content-type")
              (Std.Http.Header.Value.ofString! "multipart/form-data; boundary=b")
  let some uri := Std.Http.RequestTarget.parse? "/upload"
    | throw (IO.userError "bad target")
  let line : Std.Http.Request.Head := { method := .post, version := .v11, uri, headers }
  let raw := "--b\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\none\r\n--b\r\nContent-Disposition: form-data; name=\"b\"\r\n\r\ntwo\r\n--b--\r\n".toUTF8
  let sent ← IO.mkRef false
  let body : LeanIn.Http.Server.BodyReader :=
    { recv := fun _ => do
        let done ← (monadLift (sent.get : IO Bool) : LeanIn.Runtime.VM Bool)
        if done then pure none else do
          monadLift (sent.set true : IO Unit)
          pure (some raw)
      drained := pure true
      leftover := pure .empty }
  let fields ← runVM (multipartFields { line, body })
  unless fields == [("a", "one"), ("b", "two")] do
    throw (IO.userError s!"multipart fields {fields}")
  let stockResponse : ResponseM ContextAsync := ResponseM.text "hello"
  Async.block <| ContextAsync.run do
    let stock ← ResponseM.toStock stockResponse
    let chunk ← Std.Http.Body.recv stock.body
    let got := chunk.map (·.data) |>.getD .empty
    unless got == "hello".toUTF8 do
      throw (IO.userError "stock body")
    let streamed : ResponseM ContextAsync :=
      ResponseM.stream none (fun send => send "hello".toUTF8)
    let stock ← ResponseM.toStock streamed
    let chunk ← Std.Http.Body.recv stock.body
    let got := chunk.map (·.data) |>.getD .empty
    unless got == "hello".toUTF8 do
      throw (IO.userError "stock streamed body")

end RoutingTests.BodyHandler
