import Routing.Pattern
import Routing.Handler
import Routing.Route
import Routing.Server
import Routing.RouteTable

/-!
This library attempts to balance low ceremony with static guarantees that
a wrong-arity/wrong-type handler is a compile error

## Design overview

A route pattern string (`"/users/:id:Nat"`) parses (`Routing/Pattern.lean`)
into `List PathSeg`, plain runtime data -- no type-level encoding. From
that *value*, `HandlerType segs result` (`Routing/Handler.lean`) computes
the *type* a matching handler must have (one argument per capture,
correctly typed via `CaptureKind.type`), using Lean's dependent types
directly

`Route`/`dispatchTable` (`Routing/Route.lean`) bundle a method, pattern,
and handler into a route table, tried in order.

## Not yet supported

- **Query-string parameters** -- `dispatch` only matches the path.
- **`CaptureKind` is a closed enum** (`Nat`/`String` only). Whether to open
  it into a typeclass so downstream code can add capture types is
  deferred.
-/
