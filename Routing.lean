import Routing.Pattern
import Routing.Handler
import Routing.Route
import Routing.Server
import Routing.RouteTable
import Routing.RelativeLink

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

A `routeTable!` row can also `mount` another `routeTable!`-generated table
under a literal path prefix (`Routing/RouteTable.lean`), nesting its whole
`patterns`/`links` shape -- recursively, to whatever depth the mounted
table itself mounts further tables -- so an app can be composed from
independently-declared feature modules.

`Routing.relativeUrl` (`Routing/RelativeLink.lean`) computes a relative
link between two already-rendered `linkFor`/`.links` paths, letting code
inside a mounted module self-link using its own unprefixed `.links`
values regardless of where (or whether) the module ends up mounted --
prepending a shared literal prefix to both endpoints cancels out of the
result. `dispatch` (`Routing/Handler.lean`) tolerates a single trailing
empty path segment once a pattern is otherwise fully matched, so the
directory-style (`"."`/`".."`) references an upward relative link
resolves to still reach their target.

## Not yet supported

- **Query-string parameters** -- `dispatch` only matches the path.
- **`CaptureKind` is a closed enum** (`Nat`/`String` only). Whether to open
  it into a typeclass so downstream code can add capture types is
  deferred.
- **Captured mount prefixes** -- a `mount` prefix must be literal; mounting
  under a prefix with a `:name:Kind` capture (e.g. per-tenant routes like
  `/orgs/:orgId:Nat/...`) isn't supported yet.
-/
