/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanIn.Http.Server
public import LeanIn.Http.H1
public import Std.Http.Data
public import Routing.Route

public section

@[expose] section

namespace Routing

open Std.Http (Method Status Header Extensions RequestTarget)
open LeanIn.Http

/-- A request as the LeanIn backend sees it: the parsed head, the streaming body, the parsed target,
and the typed extensions routes and middleware share. -/
structure Request where
  head : H1.Head
  uri : RequestTarget
  method : Method
  body : LeanIn.Http.Server.BodyReader
  extensions : Extensions := Extensions.empty

/-- A buffered response returned by a route handler. The router writes it through the connection's
`ResponseWriter`; a handler that streams will need the writer form, which this cut does not expose. -/
structure Response where
  status : Nat
  reason : String
  headers : Array (String × String) := #[]
  body : ByteArray := .empty
  extensions : Extensions := Extensions.empty

/-- The HTTP status code for the `Std.Http` status values the router's response helpers use. -/
def statusCode : Status → Nat
  | .continue => 100
  | .switchingProtocols => 101
  | .processing => 102
  | .earlyHints => 103
  | .ok => 200
  | .created => 201
  | .accepted => 202
  | .nonAuthoritativeInformation => 203
  | .noContent => 204
  | .resetContent => 205
  | .partialContent => 206
  | .multiStatus => 207
  | .alreadyReported => 208
  | .imUsed => 226
  | .multipleChoices => 300
  | .movedPermanently => 301
  | .found => 302
  | .seeOther => 303
  | .notModified => 304
  | .useProxy => 305
  | .temporaryRedirect => 307
  | .permanentRedirect => 308
  | .badRequest => 400
  | .unauthorized => 401
  | .paymentRequired => 402
  | .forbidden => 403
  | .notFound => 404
  | .methodNotAllowed => 405
  | .notAcceptable => 406
  | .proxyAuthenticationRequired => 407
  | .requestTimeout => 408
  | .conflict => 409
  | .gone => 410
  | .lengthRequired => 411
  | .preconditionFailed => 412
  | .payloadTooLarge => 413
  | .uriTooLong => 414
  | .unsupportedMediaType => 415
  | .rangeNotSatisfiable => 416
  | .expectationFailed => 417
  | .imATeapot => 418
  | .misdirectedRequest => 421
  | .unprocessableEntity => 422
  | .locked => 423
  | .failedDependency => 424
  | .tooEarly => 425
  | .upgradeRequired => 426
  | .preconditionRequired => 428
  | .tooManyRequests => 429
  | .requestHeaderFieldsTooLarge => 431
  | .unavailableForLegalReasons => 451
  | .internalServerError => 500
  | .notImplemented => 501
  | .badGateway => 502
  | .serviceUnavailable => 503
  | .gatewayTimeout => 504
  | .httpVersionNotSupported => 505
  | .variantAlsoNegotiates => 506
  | .insufficientStorage => 507
  | .loopDetected => 508
  | .notExtended => 510
  | .networkAuthenticationRequired => 511
  | _ => 500

namespace Response

def ok : Response := { status := 200, reason := "OK", extensions := Extensions.empty }

def notFound : Response := { status := 404, reason := "Not Found", extensions := Extensions.empty }

def badRequest : Response := { status := 400, reason := "Bad Request", extensions := Extensions.empty }

/-- Build a response for a `Std.Http` status, carrying its reason phrase. -/
def withStatus (status : Status) : Response :=
  { status := statusCode status, reason := toString status, extensions := Extensions.empty }

/-- Add or replace a header. -/
def header (r : Response) (name : Header.Name) (value : Header.Value) : Response :=
  let key := (toString name).toLower
  { r with headers := (r.headers.filter (fun (n, _) => n.toLower != key)).push (key, toString value) }

/-- A UTF-8 text body. -/
def text (r : Response) (s : String) : Response :=
  { r with body := s.toUTF8 }

end Response

/-- The application handler: a request in, a buffered response out, both in the LeanIn VM. -/
abbrev Result := Request → LeanIn.Runtime.VM Response

/-- A handler with no captures left — the shape routes and middleware compose. `onContinue` is
kept for source compatibility with the Std-shaped router; the native driver does not issue a
100-continue negotiation. -/
structure StatelessHandler where
  onRequest : Result
  onContinue : LeanIn.Http.H1.Head → Bool := fun _ => true

instance : CoeFun StatelessHandler (fun _ => Result) := ⟨StatelessHandler.onRequest⟩

namespace Handler
def ofFn (f : Request → Response) : StatelessHandler :=
  { onRequest := fun request => pure (f request) }
end Handler

/-- Default `404 Not Found` response used by `toHandler` when no route matches. -/
def defaultNotFound : Result :=
  fun _request => pure (Response.notFound.text "Not Found")

/-- Reads back the `MatchedRoute` `toHandler` published, from a request's or a response's
`extensions`. `none` means no route matched; absence is the signal. -/
def matchedRoute? (extensions : Extensions) : Option MatchedRoute :=
  extensions.get MatchedRoute

/-- The endpoint template of the route that matched (`MatchedRoute.template`). -/
def matchedPattern? (extensions : Extensions) : Option String :=
  (matchedRoute? extensions).map (·.template)

/-- Whether a request for `path` would match one of `routes` with a trailing slash added. -/
def wantsSlash (routes : List (Route Result)) (method : Method) (path : List String) : Bool :=
  path.getLast? != some "" && (matchTable routes method (path ++ [""])).isSome

/-- Where to redirect a request that matched no route but `wantsSlash`. -/
def slashRedirect? (routes : List (Route Result)) (method : Method) (target : RequestTarget)
    (path : List String) : Option Header.Value :=
  if wantsSlash routes method path then
    let query := target.query
    Header.Value.ofString?
      (toString target.path ++ "/" ++ if query.isEmpty then "" else toString query)
  else
    none

/-- The decoded path segments that routes match against. -/
def decodedPath (target : RequestTarget) : List String :=
  target.path.toDecodedSegments.toList

/-- Dispatch and apply the matched handler; `none` if no route matched and no slash redirect applies. -/
def respond? (routes : List (Route Result)) (request : Request) : Option Result :=
  let path := decodedPath request.uri
  match matchTable routes request.method path with
  | some (matched, handler) => some fun request => do
      let response ← handler { request with extensions := request.extensions.insert matched }
      return { response with extensions := response.extensions.insert matched }
  | none =>
      (slashRedirect? routes request.method request.uri path).map fun location =>
        fun _ => pure (((Response.withStatus .permanentRedirect).header .location location).text "")

/-- Run a request through the router and return its response. -/
def runRequest (routes : List (Route Result)) (request : Request)
    (notFound : Result := defaultNotFound) : LeanIn.Runtime.VM Response :=
  match respond? routes request with
  | some response => response request
  | none => notFound request

/-- Adapt a router to a `StatelessHandler`, preserving the upstream meaning of `toHandler`:
dispatch, run the matched handler, and return the response. -/
def toHandler (routes : List (Route Result)) (notFound : Result := defaultNotFound) :
    StatelessHandler :=
  { onRequest := fun request => runRequest routes request notFound }

/-- Adapt a router to LeanIn's streaming connection handler. The body is available to handlers
through `Request.body`; the response is buffered because `Result` carries a `Response` value. -/
def toStreamHandler (routes : List (Route Result)) (notFound : Result := defaultNotFound) :
    LeanIn.Http.Server.StreamHandler :=
  fun head body writer => do
    match RequestTarget.parse? head.targetString with
    | none =>
      writer.start { status := 400, reason := "Bad Request" }
      writer.write "Bad Request".toUTF8
      writer.finish
    | some uri =>
      match Method.ofString? head.methodTokenString with
      | none =>
        writer.start { status := 501, reason := "Not Implemented" }
        writer.write "Not Implemented".toUTF8
        writer.finish
      | some method =>
        let request : Request := { head, uri, method, body }
        let response ← runRequest routes request notFound
        let headers := if response.headers.any (fun (n, _) => n.toLower == "content-length") then
            response.headers
          else response.headers.push ("content-length", toString response.body.size)
        writer.start { status := response.status, reason := response.reason, headers }
        writer.write response.body
        writer.finish

end Routing
