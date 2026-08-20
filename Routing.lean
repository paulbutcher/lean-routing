/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Pattern
public import Routing.Handler
public import Routing.Route
public import Routing.Server
public import Routing.RouteTable
public import Routing.RouteMount
public import Routing.RelativeLink

/-!
This library attempts to balance low ceremony with static guarantees that
a wrong-arity/wrong-type handler is a compile error

## Design overview

A route pattern string (`"/users/:id:Nat"`) parses (`Routing/Pattern.lean`)
into `List PathSeg`, plain runtime data, with no type-level encoding. From
that *value*, `HandlerType segs result` (`Routing/Handler.lean`) computes
the *type* a matching handler must have (one argument per capture,
correctly typed via `CaptureKind.type`), using Lean's dependent types
directly

`Route`/`dispatchTable` (`Routing/Route.lean`) bundle a method, pattern,
and handler into a route table, tried in order. `matchTable` is
`dispatchTable` plus the identity of the route that matched
(`MatchedRoute`); `toHandler` (`Routing/Server.lean`) publishes that on the
request it passes down *and* on the response it returns, since a middleware
wrapping the router has only the response to read it from.
`Routing.matchedPattern?` renders that route back as `"/users/:id"`: an
endpoint's identity, which drops each capture's kind and so holds still
when the kind changes, as against `renderPattern`'s `"/users/:id:Nat"`,
which reproduces the pattern's source text and parses back.

A `route_table` row can also `mount` another `route_table`-generated table
under a literal path prefix (`Routing/RouteTable.lean`), nesting its whole
`patterns`/`links` shape, recursively, to whatever depth the mounted
table itself mounts further tables, so an app can be composed from
independently-declared feature modules.

`Routing.relativeUrl` (`Routing/RelativeLink.lean`) computes a relative
link between two already-rendered `linkFor`/`.links` paths, letting code
inside a mounted module self-link using its own unprefixed `.links`
values regardless of where (or whether) the module ends up mounted:
prepending a shared literal prefix to both endpoints cancels out of the
result. `dispatch` (`Routing/Handler.lean`) tolerates a single trailing
empty path segment once a pattern is otherwise fully matched, so the
directory-style (`"."`/`".."`) references an upward relative link
resolves to still reach their target.

## Limitations

- **Query-string parameters**: `dispatch` matches the path only.
- **`CaptureKind` is a closed enum** (`Nat`/`String` only), so downstream
  code cannot add capture types of its own.
- **Captured mount prefixes**: a `mount` prefix must be literal, so routes
  cannot be mounted under a prefix containing a `:name:Kind` capture (a
  per-tenant `/orgs/:orgId:Nat/...` prefix, for instance).
-/
