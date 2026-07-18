import Std.Http.Data.Method
import Routing.Handler

/-!
Bundling a method, a path pattern, and a matching handler into a `Route`,
and dispatching an incoming `(Method, path)` against a table of them in
order.
-/

namespace Routing

open Std.Http (Method)

/-- An HTTP method, a path pattern (as already-parsed segments,
so `HandlerType segs result` -- and therefore `handler`'s arity/types --
is checked at the point the route is built), and its handler. -/
structure Route (result : Type) where
  method : Method
  segs : List PathSeg
  handler : HandlerType segs result

/-- Builds a `Route` straight from already-parsed segments -- no parsing, so no failure mode at
this call site. `segs` is meant to come from a `routeTable!`-generated `App.Patterns` value
(`RouteTable.lean`), whose pattern was already validated at the `routeTable!` row that declared
it. -/
def route (method : Method) (segs : List PathSeg) {result : Type}
    (handler : HandlerType segs result) : Route result :=
  { method, segs, handler }

/-- Per-method aliases for `route`, for `segs` sourced from a `routeTable!`-generated
`App.Patterns` value -- so a route table can write `.get`/`.post`/`.put`/`.delete` (resolved via
Lean's generalized dot notation against the list's expected `Route result` element type) instead
of `route .get`/`route .post`/etc. -/
def Route.get (segs : List PathSeg) {result : Type} (handler : HandlerType segs result) :
    Route result :=
  route .get segs handler

def Route.post (segs : List PathSeg) {result : Type} (handler : HandlerType segs result) :
    Route result :=
  route .post segs handler

def Route.put (segs : List PathSeg) {result : Type} (handler : HandlerType segs result) :
    Route result :=
  route .put segs handler

def Route.delete (segs : List PathSeg) {result : Type} (handler : HandlerType segs result) :
    Route result :=
  route .delete segs handler

/-- Matches one route against an incoming method and decoded path,
producing the handler's result applied to any extracted captures. `none`
if the method doesn't match, or if `dispatch` rejects the path (literal
mismatch, mistyped capture, or arity mismatch -- `Handler.lean`). -/
def Route.tryDispatch (r : Route result) (method : Method) (path : List String) :
    Option result :=
  if r.method == method then dispatch r.segs r.handler path else none

/-- Tries each route in order, returning the first match. Pairing this with
`Std.Http.Server.Handler` is `Server.lean`. -/
def dispatchTable (routes : List (Route result)) (method : Method) (path : List String) :
    Option result :=
  routes.findSome? (Route.tryDispatch · method path)

end Routing
