/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Http.Server
public import Routing.Route

public section

@[expose] section

namespace Routing

open Std Async
open Std Http Server

abbrev Result := Request Body.Stream → ContextAsync (Response Body.Any)

/-- Default `404 Not Found` response used by `toHandler` when no route
matches. -/
def defaultNotFound : Result :=
  fun _request => Response.notFound.text "Not Found"

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

/-- Where to redirect a request that matched no route but would match with a trailing slash, as a
mounted index does (`mountSegs`, `Pattern.lean`): its target with the slash added, query intact.
Serving the slashless form instead would break relative links from that page. -/
def slashRedirect? (routes : List (Route Result)) (method : Method) (target : RequestTarget)
    (path : List String) : Option Header.Value :=
  if path.getLast? != some "" && (matchTable routes method (path ++ [""])).isSome then
    let query := target.query
    Header.Value.ofString?
      (toString target.path ++ "/" ++ if query.isEmpty then "" else toString query)
  else
    none

/-- Wires a route table into a `Std.Http.Server.Handler`: decodes the
incoming request's method and path (`RequestTarget.path.toDecodedSegments`
feeds `dispatch` via `matchTable`), tries each route in order, and
applies the matched handler (or `notFound`) to the full request. A request that matches nothing
but would with a trailing slash gets a `308` there instead (`slashRedirect?`).

The matched route is published (as a `MatchedRoute` extension, read back with `matchedRoute?`)
in *both* directions, because they reach different readers. The request copy is visible to the
matched handler and to anything the router calls into. The response copy is the one visible to
middleware *wrapping* `toHandler`: such middleware has already passed its request downwards by the
time matching happens, so the response is the only channel that travels back up to it. -/
def toHandler (routes : List (Route Result)) (notFound : Result := defaultNotFound) :
    StatelessHandler :=
  Handler.ofFn fun request =>
    let path := request.line.uri.path.toDecodedSegments.toList
    match matchTable routes request.line.method path with
    | some (matched, handler) => do
        let response ← handler { request with extensions := request.extensions.insert matched }
        return { response with extensions := response.extensions.insert matched }
    | none =>
        match slashRedirect? routes request.line.method request.line.uri path with
        | some location =>
            Response.withStatus .permanentRedirect |>.header Header.Name.location location |>.text ""
        | none => notFound request

end Routing
