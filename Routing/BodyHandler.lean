/-
A routing result whose response body is a `Body.ResponseBody`. This is the generic entry point for
streamed or deferred bodies; the existing `Result` remains the buffered byte-array alias.
-/
module

public import Routing.Body

public section

namespace Routing

open Std.Http (Status Header Extensions)
open LeanIn.Http

/-- The stock status for a numeric routing status. -/
def statusOfNat (n : Nat) (reason : String) : Status :=
  let code := n.toUInt16
  match Status.ofCode none code with
  | some status => status
  | none =>
    match Std.Http.CustomStatus.ofCodeAndPhrase? code reason with
    | some custom => .other custom
    | none => .internalServerError

/-- Convert routing's string headers. Invalid names/values are skipped on this metadata-only path. -/
def headersOf (headers : Array (String × String)) : Std.Http.Headers :=
  headers.foldl (fun acc (name, value) =>
    match Header.Name.ofString? name, Header.Value.ofString? value with
    | some n, some v => acc.insert n v
    | _, _ => acc) .empty

/-- A buffered or streamed response. -/
structure ResponseM (m : Type → Type) where
  status : Nat := 200
  reason : String := "OK"
  headers : Array (String × String) := #[]
  body : Body.ResponseBody m
  extensions : Extensions := Extensions.empty

namespace ResponseM

def ok (body : Body.ResponseBody m) : ResponseM m := { body }

def bytes (data : ByteArray) : ResponseM m := { body := .bytes data }

def text (s : String) : ResponseM m := bytes s.toUTF8

def stream (length? : Option Nat) (write : (ByteArray → m Unit) → m Unit) : ResponseM m :=
  { body := .stream length? write }

def setStatus (r : ResponseM m) (status : Nat) (reason : String) : ResponseM m :=
  { r with status, reason }

def header (r : ResponseM m) (name : String) (value : String) : ResponseM m :=
  { r with headers := r.headers.push (name, value) }

end ResponseM

/-- A request handler whose response body is the shared body value. -/
structure BodyHandlerM (m : Type → Type) [Monad m] (ReqBody : Type) where
  onRequest : RequestM ReqBody → m (ResponseM m)
  onContinue : Std.Http.Request.Head → Bool := fun _ => true

abbrev BodyResultM (m : Type → Type) (ReqBody : Type) := RequestM ReqBody → m (ResponseM m)

/-- The LeanIn response value for a generic response. -/
def ResponseM.toLeanIn (r : ResponseM LeanIn.Runtime.VM) :
    Std.Http.Response LeanIn.Http.ResponseBody :=
  { line := { status := statusOfNat r.status r.reason, version := .v11, headers := headersOf r.headers }
    body := Body.ResponseBody.toLeanIn r.body
    extensions := r.extensions }

/-- The stock response value for a generic response. -/
def ResponseM.toStock (r : ResponseM Std.Async.ContextAsync) :
    Std.Async.ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  let body ← Body.ResponseBody.toStock r.body
  let line : Std.Http.Response.Head :=
    { status := statusOfNat r.status r.reason, version := .v11, headers := headersOf r.headers }
  pure { line, body, extensions := r.extensions }

/-- Dispatch a body-valued route table. -/
def respond?BodyM {m : Type → Type} [Monad m] {ReqBody : Type}
    (routes : RouteIndex (BodyResultM m ReqBody)) (request : RequestM ReqBody) :
    Option (BodyResultM m ReqBody) :=
  let path := decodedPath request.line.uri
  match routes.matchTable request.line.method path with
  | some (matched, handler) => some fun request => do
      let response ← handler { request with extensions := request.extensions.insert matched }
      return { response with extensions := response.extensions.insert matched }
  | none =>
      (slashRedirect? routes request.line.method request.line.uri path).map fun location =>
        fun _ => pure { status := 308, reason := "Permanent Redirect"
                        headers := #[("location", toString location)]
                        body := .bytes .empty }

def runRequestBodyM {m : Type → Type} [Monad m] {ReqBody : Type}
    (routes : List (Route (BodyResultM m ReqBody))) (request : RequestM ReqBody)
    (notFound : BodyResultM m ReqBody := fun _ => pure (ResponseM.text "Not Found" |>.setStatus 404 "Not Found")) :
    m (ResponseM m) :=
  let index := RouteIndex.of routes
  match respond?BodyM index request with
  | some response => response request
  | none => notFound request

def toBodyHandlerM {m : Type → Type} [Monad m] {ReqBody : Type}
    (routes : List (Route (BodyResultM m ReqBody)))
    (notFound : BodyResultM m ReqBody := fun _ => pure (ResponseM.text "Not Found" |>.setStatus 404 "Not Found")) :
    BodyHandlerM m ReqBody :=
  let index := RouteIndex.of routes
  { onRequest := fun request => runRequestBodyM routes request notFound }

/-- The native adapter: stream the body through the response writer. -/
def toStreamHandlerBodyOf (handler : BodyHandlerM LeanIn.Runtime.VM LeanIn.Http.Server.BodyReader) :
    LeanIn.Http.Server.StreamHandler :=
  fun head body writer => do
    match LeanIn.Http.StdHandler.headToStock head with
    | .error _ =>
      writer.start { status := 400, reason := "Bad Request" }
      writer.write "Bad Request".toUTF8
      writer.finish
    | .ok line =>
      let request : Request := { line, body }
      if LeanIn.Http.H1.expectsContinue head && handler.onContinue line then
        writer.sendContinue
      let response ← handler.onRequest request
      LeanIn.Http.StdHandler.writeResponse writer (ResponseM.toLeanIn response) true (line.method == .head)

/-- The stock adapter: buffer the body where the stock response type cannot stream it. -/
def toStockHandlerBodyOf (handler : BodyHandlerM Std.Async.ContextAsync Std.Http.Body.Stream) :
    Std.Http.Server.StatelessHandler :=
  { onRequest := fun request => do
      let response ← handler.onRequest
        { line := request.line, body := request.body, extensions := request.extensions }
      ResponseM.toStock response
    onContinue := fun head => pure (handler.onContinue head) }

end Routing
end
