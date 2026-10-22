import Routing.BodyHandler
import Routing.Pilot

/-!
The body-valued result on both hosts: the same handler value is converted to LeanIn's response
and to the stock response, and a static-file handler type-checks at both instantiations.
-/

namespace RoutingTests.BodyHandler

open Std Async
open Routing

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

#eval show IO Unit from do
  let response : ResponseM LeanIn.Runtime.VM := ResponseM.text "hello"
  let native := ResponseM.toLeanIn response
  unless native.line.status == .ok do
    throw (IO.userError "native status")
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
