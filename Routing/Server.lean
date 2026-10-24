/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Engine
public import Routing.Trie

public section

@[expose] section

namespace Routing

open Std Http

/-- Default `404 Not Found` response used by `toHandler` when no route
matches. -/
def defaultNotFound {e : Engine} : Result e :=
  fun _request => e.text Response.notFound "Not Found"

/-- Reads back the `MatchedRoute` `toHandler` published, from a request's or a response's
`extensions`. `none` means no route matched; absence is the signal, so a 404 is distinguishable
from a match rather than reported as an empty or guessed pattern. -/
def matchedRoute? (extensions : Extensions) : Option MatchedRoute :=
  extensions.get MatchedRoute

/-- The endpoint template of the route that matched (`MatchedRoute.template`), from a request's or
a response's `extensions`; `none` where `matchedRoute?` gives `none`.

Provided as a value telemetry middleware can be handed directly, supplying both an `http.route`
attribute and the span name built from it, so no consumer hand-rolls the composition and reaches
for `renderPattern` on the way. -/
def matchedPattern? (extensions : Extensions) : Option String :=
  (matchedRoute? extensions).map (·.template)

/-- Whether a request for `path` would match one of `routes` with a trailing slash added, as a
mounted index does (`mountSegs`, `Pattern.lean`). -/
def wantsSlash (routes : RouteIndex result) (method : Method) (path : List String) : Bool :=
  path.getLast? != some "" && (routes.matchTable method (path ++ [""])).isSome

/-- `target` with a slash added, query intact, written as `encodedPath` writes a link. -/
def slashLocation (target : RequestTarget) : String :=
  encodedPath (target.path.segments.toList.map toString ++ [""]) ++
    if target.query.isEmpty then "" else toString target.query

/-- Where to redirect a request that matched no route but `wantsSlash`: `slashLocation`. Serving
the slashless form instead would break relative links from that page. -/
def slashRedirect? (routes : RouteIndex result) (method : Method) (target : RequestTarget)
    (path : List String) : Option Header.Value :=
  if wantsSlash routes method path then Header.Value.ofString? (slashLocation target) else none

/-- The decoded path segments that routes match against, without the `.` that `encodedPath` writes
before an empty first segment. A client removes that `.` before sending, and one that sends the
link as written still matches. A `.` anywhere else stays, so `/./x` matches no route. -/
def decodedPath (target : RequestTarget) : List String :=
  match target.path.toDecodedSegments.toList with
  | "." :: "" :: rest => "" :: rest
  | segs => segs

/-- Decodes the request's method and path (`decodedPath` feeds `dispatch` via
`RouteIndex.matchTable`), finds the first route that matches, and applies its handler to the full
request.
A request that matches nothing but would with a trailing slash gets a `308` there instead
(`slashRedirect?`). `none` if neither.

The matched route is published (as a `MatchedRoute` extension, read back with `matchedRoute?`)
in *both* directions, because they reach different readers. The request copy is visible to the
matched handler and to anything the router calls into. The response copy is the one visible to
middleware *wrapping* the router: such middleware has already passed its request downwards by the
time matching happens, so the response is the only channel that travels back up to it. -/
def respond? {e : Engine} (routes : RouteIndex (Result e)) (request : Request e.ReqBody) :
    Option (e.M (Response e.RespBody)) :=
  let path := decodedPath request.line.uri
  match routes.matchTable request.line.method path with
  | some (matched, handler) => some do
      let response ← handler { request with extensions := request.extensions.insert matched }
      return { response with extensions := response.extensions.insert matched }
  | none =>
      (slashRedirect? routes request.line.method request.line.uri path).map fun location =>
        e.text (Response.withStatus .permanentRedirect |>.header Header.Name.location location) ""

/-- Wires a route table into a `StatelessHandler`, answering with `respond?`, else with
`notFound`. -/
def RouteIndex.toHandler {e : Engine} (routes : RouteIndex (Result e))
    (notFound : Result e := defaultNotFound) : StatelessHandler e :=
  .ofFn fun request => (respond? routes request).getD (notFound request)

/-- `RouteIndex.toHandler` over `RouteIndex.of routes`, so build the handler once. -/
def toHandler {e : Engine} (routes : List (Route (Result e)))
    (notFound : Result e := defaultNotFound)
    (h : Internal.unshadowed (routes.map Route.key) = true := by routes_unshadowed) :
    StatelessHandler e :=
  (RouteIndex.of routes h).toHandler notFound

end Routing
