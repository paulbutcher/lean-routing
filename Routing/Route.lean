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

/-- Builds a `Route` from a method, a pattern *string*, and a handler. The pattern is parsed with
`parsePattern!`, which fails to compile on a malformed pattern -- acceptable here because route
patterns are source-code literals written by the route author, so a malformed one is a
programming error that should be an elaboration error right at this call, not something to
recover from at request time (`Pattern.lean`'s `parsePattern!` docstring). `h` re-derives
`parsePattern!`'s own `autoParam` explicitly (rather than leaving each call below to its own
default) so both calls agree on one proof and `route` itself still elaborates with `pattern`
symbolic. -/
def route (method : Method) (pattern : String) {result : Type}
    (h : (parsePattern pattern).isSome := by decide)
    (handler : HandlerType (parsePattern! pattern h) result) : Route result :=
  { method, segs := parsePattern! pattern h, handler }

/-- Per-method aliases for `route`, so a route table can write `.get`/`.post`/`.put`/`.delete`
(resolved via Lean's generalized dot notation against the list's expected `Route result` element
type) instead of `route .get`/`route .post`/etc. -/
def Route.get (pattern : String) {result : Type}
    (h : (parsePattern pattern).isSome := by decide)
    (handler : HandlerType (parsePattern! pattern h) result) : Route result :=
  route .get pattern h handler

def Route.post (pattern : String) {result : Type}
    (h : (parsePattern pattern).isSome := by decide)
    (handler : HandlerType (parsePattern! pattern h) result) : Route result :=
  route .post pattern h handler

def Route.put (pattern : String) {result : Type}
    (h : (parsePattern pattern).isSome := by decide)
    (handler : HandlerType (parsePattern! pattern h) result) : Route result :=
  route .put pattern h handler

def Route.delete (pattern : String) {result : Type}
    (h : (parsePattern pattern).isSome := by decide)
    (handler : HandlerType (parsePattern! pattern h) result) : Route result :=
  route .delete pattern h handler

/-- Matches one route against an incoming method and decoded path,
producing the handler's result applied to any extracted captures. `none`
if the method doesn't match, or if `dispatch` rejects the path (literal
mismatch, mistyped capture, or arity mismatch -- `Handler.lean`). -/
def Route.tryDispatch (r : Route result) (method : Method) (path : List String) :
    Option result :=
  if r.method == method then dispatch r.segs r.handler path else none

/-- Tries each route in order, returning the first match. This is the
"table of routes" half of `docs/routing-design-plan.md` §5's wiring step;
pairing it with `Std.Http.Server.Handler` is `Server.lean`. -/
def dispatchTable (routes : List (Route result)) (method : Method) (path : List String) :
    Option result :=
  routes.findSome? (Route.tryDispatch · method path)

end Routing
