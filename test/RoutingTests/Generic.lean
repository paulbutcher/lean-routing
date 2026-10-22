import Routing.Stock

/-!
The same route declaration instantiated at both hosts. The body type and monad are parameters; the
route source itself is not duplicated.
-/

namespace RoutingTests.Generic

open Std Async
open Std.Http
open Routing

/-- One route source, polymorphic in the request body and computation monad. -/
def sharedRoutes {m : Type → Type} [Monad m] {ReqBody : Type} : List (Route (ResultM m ReqBody)) :=
  [ .get [.lit "hello"] (handler := fun _ => pure (Response.ok.text "hello")) ]

/-- The LeanIn instantiation. -/
def nativeRoutes : List (Route Result) := sharedRoutes

/-- The stock instantiation. -/
def stockRoutes : List (Route Stock.Result) := sharedRoutes

def nativeHandler : StatelessHandler := toHandler nativeRoutes

def stockHandler : Std.Http.Server.StatelessHandler := Stock.toStatelessHandler stockRoutes

private def emptyBody : LeanIn.Http.Server.BodyReader :=
  { recv := fun _ => pure none, drained := pure true, leftover := pure .empty }

private def runVM (m : LeanIn.Runtime.VM α) : IO α := do
  let cell ← LeanIn.Runtime.RawCell.new (α := α)
  LeanIn.Runtime.VM.runToCell m cell
  let out ← IO.mkRef (none : Option α)
  LeanIn.Runtime.RawCell.await cell (fun v => out.set (some v))
  match ← out.get with
  | some v => pure v
  | none => throw (IO.userError "test VM suspended")

#eval show IO Unit from do
  let some uri := RequestTarget.parse? "/hello"
    | throw (IO.userError "bad target")
  let line : Std.Http.Request.Head := { method := .get, version := .v11, uri }
  let native ← runVM (nativeHandler.onRequest { line, body := emptyBody })
  unless native.status == 200 do
    throw (IO.userError s!"native status {native.status}")
  Async.block <| ContextAsync.run do
    let body ← Std.Http.Body.mkStream
    let response ← stockHandler.onRequest { line, body }
    unless response.line.status == .ok do
      throw (IO.userError s!"stock status {response.line.status}")

end RoutingTests.Generic
