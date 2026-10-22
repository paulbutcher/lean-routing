/-
A native streaming route API: the handler receives LeanIn's `ResponseWriter` and writes the body
incrementally. This is an extension, not an upstream parity item; the buffered `Routing.Result`
remains the default.
-/
module

public import Routing.Server

public section

namespace Routing.Streaming

open Std.Http (Method Status Header)

abbrev Result := Request → LeanIn.Http.Server.ResponseWriter → LeanIn.Runtime.VM Unit

def notFound : Result := fun _ w => do
  w.start { status := 404, reason := "Not Found" }
  w.write "Not Found".toUTF8
  w.finish

def respond? (routes : RouteIndex Result) (request : Request)
    (w : LeanIn.Http.Server.ResponseWriter) : Option (LeanIn.Runtime.VM Unit) :=
  match routes.matchTable request.method (decodedPath request.uri) with
  | some (matched, handler) =>
    some (handler { request with extensions := request.extensions.insert matched } w)
  | none =>
    (slashRedirect? routes request.method request.uri (decodedPath request.uri)).map fun location => do
      w.start { status := 308, reason := "Permanent Redirect", headers := #[("location", toString location)] }
      w.finish

def toStreamHandler (routes : List (Route Result)) (missing : Result := notFound) :
    LeanIn.Http.Server.StreamHandler :=
  let index := RouteIndex.of routes
  fun head body writer => do
    match Std.Http.RequestTarget.parse? head.targetString with
    | none =>
      writer.start { status := 400, reason := "Bad Request" }
      writer.finish
    | some uri =>
      match Method.ofString? head.methodTokenString with
      | none =>
        writer.start { status := 501, reason := "Not Implemented" }
        writer.finish
      | some method =>
        let request : Request := { head, uri, method, body }
        match respond? index request writer with
        | some action => action
        | none => missing request writer

end Routing.Streaming
