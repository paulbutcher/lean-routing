/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanIn.Http.Server
public import LeanIn.Http.StdHandler
public import LeanIn.Http.H1
public import Std.Http.Data
public import Routing.Route
public import Routing.Trie

public section

@[expose] section

namespace Routing

open Std.Http (Method Status Header Extensions RequestTarget)
open LeanIn.Http

/-- A request over a host body type. The line is `Std.Http` metadata in both hosts; the native
adapter converts the parsed H1 head once at dispatch. -/
structure RequestM (Body : Type) where
  line : Std.Http.Request.Head
  body : Body
  extensions : Std.Http.Extensions := .empty

/-- The native request: LeanIn's streaming body reader. -/
abbrev Request := RequestM LeanIn.Http.Server.BodyReader

/-- The request line, in the shape upstream code reads (`request.line.uri`, `.method`,
`.version`). -/
abbrev RequestLine := Std.Http.Request.Head

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

def plain (r : Response) (s : String) : Response :=
  r.header (.mk "content-type") (.mk "text/plain; charset=utf-8") |>.text s

def html (r : Response) (s : String) : Response :=
  r.header (.mk "content-type") (.mk "text/html; charset=utf-8") |>.text s

end Response

/-- The application handler: a request body type, a computation monad, and a buffered `Response`. -/
abbrev ResultM (m : Type → Type) (ReqBody : Type) := RequestM ReqBody → m Response

/-- The native result: LeanIn's reader and `VM`. -/
abbrev Result := ResultM LeanIn.Runtime.VM LeanIn.Http.Server.BodyReader

/-- A handler with no captures left, parameterized over its computation and request body. `onContinue`
takes the same `Std.Http` head the rest of the surface uses. -/
structure StatelessHandlerM (m : Type → Type) [Monad m] (ReqBody : Type) where
  onRequest : ResultM m ReqBody
  onContinue : Std.Http.Request.Head → Bool := fun _ => true

/-- The native stateless handler. -/
abbrev StatelessHandler := StatelessHandlerM LeanIn.Runtime.VM LeanIn.Http.Server.BodyReader

instance {m : Type → Type} [Monad m] {ReqBody : Type} :
    CoeFun (StatelessHandlerM m ReqBody) (fun _ => ResultM m ReqBody) :=
  ⟨StatelessHandlerM.onRequest⟩

namespace Handler
/-- Lift a pure handler into any monad and body type. -/
def ofFnM {m : Type → Type} [Monad m] {ReqBody : Type}
    (f : RequestM ReqBody → Response) : StatelessHandlerM m ReqBody :=
  { onRequest := fun request => pure (f request) }

/-- The native `ofFn`. -/
def ofFn (f : Request → Response) : StatelessHandler :=
  ofFnM (m := LeanIn.Runtime.VM) f
end Handler

/-- Default `404 Not Found` response used by `toHandler` when no route matches. -/
def defaultNotFoundM {m : Type → Type} [Monad m] {ReqBody : Type} : ResultM m ReqBody :=
  fun _request => pure (Response.notFound.text "Not Found")

def defaultNotFound : Result := defaultNotFoundM

/-- Reads back the `MatchedRoute` `toHandler` published, from a request's or a response's
`extensions`. `none` means no route matched; absence is the signal. -/
def matchedRoute? (extensions : Extensions) : Option MatchedRoute :=
  extensions.get MatchedRoute

/-- The endpoint template of the route that matched (`MatchedRoute.template`). -/
def matchedPattern? (extensions : Extensions) : Option String :=
  (matchedRoute? extensions).map (·.template)

/-- Whether a request for `path` would match one of `routes` with a trailing slash added, as a
mounted index does (`mountSegs`, `Pattern.lean`). -/
def wantsSlash (routes : RouteIndex result) (method : Method) (path : List String) : Bool :=
  path.getLast? != some "" && (routes.matchTable method (path ++ [""])).isSome

/-- Where to redirect a request that matched no route but `wantsSlash`: its target with the slash
added, query intact. Serving the slashless form instead would break relative links from that
page. -/
def slashRedirect? (routes : RouteIndex result) (method : Method) (target : RequestTarget)
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

/-- Dispatch and apply the matched handler; `none` if no route matched and no slash redirect applies.
The index is built once, by `toHandler` or `runRequest`'s caller. -/
def respond?M {m : Type → Type} [Monad m] {ReqBody : Type}
    (routes : RouteIndex (ResultM m ReqBody)) (request : RequestM ReqBody) :
    Option (ResultM m ReqBody) :=
  let path := decodedPath request.line.uri
  match routes.matchTable request.line.method path with
  | some (matched, handler) => some fun request => do
      let response ← handler { request with extensions := request.extensions.insert matched }
      return { response with extensions := response.extensions.insert matched }
  | none =>
      (slashRedirect? routes request.line.method request.line.uri path).map fun location =>
        fun _ => pure (((Response.withStatus .permanentRedirect).header .location location).text "")

/-- Run a request through an existing index. -/
def runRequestAtM {m : Type → Type} [Monad m] {ReqBody : Type}
    (routes : RouteIndex (ResultM m ReqBody)) (request : RequestM ReqBody)
    (notFound : ResultM m ReqBody := defaultNotFoundM) : m Response :=
  match respond?M routes request with
  | some response => response request
  | none => notFound request

/-- Run a list of routes through a freshly built index. -/
def runRequestM {m : Type → Type} [Monad m] {ReqBody : Type}
    (routes : List (Route (ResultM m ReqBody))) (request : RequestM ReqBody)
    (notFound : ResultM m ReqBody := defaultNotFoundM) : m Response :=
  runRequestAtM (RouteIndex.of routes) request notFound

/-- Adapt a router to a stateless handler, preserving the upstream meaning of `toHandler`:
dispatch, run the matched handler, and return the response. The index is built once here. -/
def toHandlerM {m : Type → Type} [Monad m] {ReqBody : Type}
    (routes : List (Route (ResultM m ReqBody))) (notFound : ResultM m ReqBody := defaultNotFoundM) :
    StatelessHandlerM m ReqBody :=
  let index := RouteIndex.of routes
  { onRequest := fun request => runRequestAtM index request notFound }

/-- The native `respond?`. -/
def respond? (routes : RouteIndex Result) (request : Request) : Option Result :=
  respond?M routes request

/-- The native `runRequestAt`. -/
def runRequestAt (routes : RouteIndex Result) (request : Request)
    (notFound : Result := defaultNotFound) : LeanIn.Runtime.VM Response :=
  runRequestAtM routes request notFound

/-- The native `runRequest`. -/
def runRequest (routes : List (Route Result)) (request : Request)
    (notFound : Result := defaultNotFound) : LeanIn.Runtime.VM Response :=
  runRequestM routes request notFound

/-- The native `toHandler`. -/
def toHandler (routes : List (Route Result)) (notFound : Result := defaultNotFound) :
    StatelessHandler :=
  toHandlerM routes notFound

/-- Adapt a `StatelessHandler` to LeanIn's streaming connection handler. The body is available to
handlers through `Request.body`; the response is buffered because `Result` carries a `Response`
value. When the driver has `autoContinue` off, `onContinue` decides the interim response. -/
def toStreamHandlerOf (handler : StatelessHandler) : LeanIn.Http.Server.StreamHandler :=
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
      let headers := if response.headers.any (fun (n, _) => n.toLower == "content-length") then
          response.headers
        else response.headers.push ("content-length", toString response.body.size)
      writer.start { status := response.status, reason := response.reason, headers }
      writer.write response.body
      writer.finish

/-- Adapt a route table to LeanIn's connection handler. -/
def toStreamHandler (routes : List (Route Result)) (notFound : Result := defaultNotFound) :
    LeanIn.Http.Server.StreamHandler :=
  toStreamHandlerOf (toHandler routes notFound)

end Routing
