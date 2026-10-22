/-
A stock `Std.Http.Server` adapter for the parameterized routing result. The same route source can be
instantiated at `ContextAsync`/`Body.Stream`; the adapter converts the buffered routing response into
the stock `Body.Any` response at dispatch.
-/
module

public import Routing.Server
public import Std.Http.Server

public section

namespace Routing.Stock

open Std Async
open Std.Http Server

/-- A route result on the stock server. -/
abbrev Result := ResultM ContextAsync Body.Stream

/-- The stock response status for a numeric routing status. Named codes stay named; an unknown code
uses `Status.other`, and an invalid custom status falls back to `500` rather than silently becoming `200`. -/
def statusOfNat (n : Nat) (reason : String) : Status :=
  let code := n.toUInt16
  match Status.ofCode none code with
  | some status => status
  | none =>
    match CustomStatus.ofCodeAndPhrase? code reason with
    | some custom => .other custom
    | none => .internalServerError

def headersOf (headers : Array (String × String)) : Except IO.Error Std.Http.Headers := do
  let mut acc := Std.Http.Headers.empty
  for (name, value) in headers do
    let some n := Header.Name.ofString? name
      | throw (.userError s!"routing: invalid response header name {name.quote}")
    let some v := Header.Value.ofString? value
      | throw (.userError s!"routing: invalid response header value {value.quote}")
    acc := acc.insert n v
  return acc

/-- Convert a buffered routing response to the stock response type. -/
def responseOf (response : Response) : ContextAsync (Std.Http.Response Body.Any) := do
  let body ← (Std.Http.Body.Full.ofByteArray response.body : Async Body.Full)
  let headers ← match headersOf response.headers with
    | .ok headers => pure headers
    | .error e => throw e
  let line : Std.Http.Response.Head :=
    { status := statusOfNat response.status response.reason
      version := .v11
      headers }
  return { line, body := Std.Http.Body.Any.ofBody body, extensions := response.extensions }

/-- Serve a generic stock handler on `Std.Http.Server`. -/
def toStatelessHandlerOf (handler : StatelessHandlerM ContextAsync Body.Stream) :
    Std.Http.Server.StatelessHandler :=
  { onRequest := fun request => do
      let response ← handler.onRequest
        { line := request.line, body := request.body, extensions := request.extensions }
      responseOf response
    onContinue := fun head => pure (handler.onContinue head) }

/-- Serve a route table on `Std.Http.Server`. -/
def toStatelessHandler (routes : List (Route Result))
    (notFound : Result := fun _ => pure (Response.notFound.text "Not Found")) :
    Std.Http.Server.StatelessHandler :=
  toStatelessHandlerOf (toHandlerM routes notFound)

end Routing.Stock
end
