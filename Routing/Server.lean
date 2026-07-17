import Std.Http.Server
import Routing.Route

namespace Routing

open Std Async
open Std Http Server

abbrev Result := Request Body.Stream → ContextAsync (Response Body.Any)

/-- Default `404 Not Found` response used by `toHandler` when no route
matches. -/
def defaultNotFound : Result :=
  fun _request => Response.notFound.text "Not Found"

/-- Wires a route table into a `Std.Http.Server.Handler`: decodes the
incoming request's method and path (`RequestTarget.path.toDecodedSegments`
feeds `dispatch` via `dispatchTable`), tries each route in order, and
applies the matched handler (or `notFound`) to the full request. -/
def toHandler (routes : List (Route Result)) (notFound : Result := defaultNotFound) :
    StatelessHandler :=
  Handler.ofFn fun request =>
    let path := request.line.uri.path.toDecodedSegments.toList
    match dispatchTable routes request.line.method path with
    | some handler => handler request
    | none => notFound request

end Routing
