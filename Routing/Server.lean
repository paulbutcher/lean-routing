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

Telemetry middleware wants exactly this composition, and wants it as a value it can be handed:
one function supplying both an `http.route` attribute and the span name built from it. Provided
here so no consumer hand-rolls it and reaches for `renderPattern` on the way. -/
def matchedPattern? (extensions : Extensions) : Option String :=
  (matchedRoute? extensions).map (·.template)

/-- Wires a route table into a `Std.Http.Server.Handler`: decodes the
incoming request's method and path (`RequestTarget.path.toDecodedSegments`
feeds `dispatch` via `matchTable`), tries each route in order, and
applies the matched handler (or `notFound`) to the full request.

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
    | none => notFound request

end Routing
