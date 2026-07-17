# Routing

A typed HTTP router for Lean 4 / [`Std.Http`](https://github.com/leanprover/std4). Route
patterns like `"/users/:id:Nat"` determine the exact type your handler must have — a
wrong-arity or wrong-type handler is a compile error, not a runtime bug.

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "routing"
git = "https://github.com/paulbutcher/lean-routing.git"
```

## Usage

### 1. Declare your routes

```lean
import Routing.RouteTable

routeTable! App
  [ "/" as index,
    "/users/:id:Nat" as user,
    "/users/:id:Nat/posts/:slug:String" as userPost ]
```

This parses each pattern immediately, so a malformed one is a compile error right here, at the
row that wrote it. It generates `App.patterns.index`/... (the parsed patterns, for step 2) and
`App.links.index`/... (link-building functions — see below), all under one name, `App`.

### 2. Attach handlers and build the route table

```lean
import Routing.Route

open Routing

def routes : List (Route Result) :=
  [ .get App.patterns.index (handler := fun request => Response.ok.text "home"),
    .get App.patterns.user (handler := fun (id : Nat) request =>
      Response.ok.text s!"user #{id}"),
    .post App.patterns.userPost (handler := fun (id : Nat) (slug : String) request =>
      Response.ok.text s!"user #{id}, post {slug}") ]
```

Building from `App.patterns` (rather than a pattern string) means this step never re-parses or
re-validates a pattern — that already happened in step 1.

The handler takes one argument per capture in the pattern (`:id:Nat` → `Nat`, `:slug:String`
→ `String`), in order, followed by the request itself. Getting the arity or types wrong is a
compile error.

### 3. Wire into a server

```lean
import Routing.Server

def main : IO Unit := do
  ... Std.Http.Server.run (Routing.toHandler routes) ...
```

Unmatched requests get a default `404 Not Found`; pass `notFound := ...` to `toHandler` to
override it.

### Generating links

Use `App.links.<name>` anywhere you need a URL for one of your routes, e.g. in a template:

```lean
#eval App.links.index       -- "/"
#eval App.links.user 42     -- "/users/42"
```

`App.links.user` is a function (`Nat → String`) because its pattern has one capture; a
pattern with no captures gives a plain `String`. Building links this way means a typo in a
pattern, or a pattern that changes shape, is caught at compile time everywhere it's linked
from.

### One-off routes without `routeTable!`

For a route that doesn't need a name or a link, `.getPattern`/`.postPattern`/`.putPattern`/
`.deletePattern` take a pattern string directly (parsed, and validated, right there):

```lean
.getPattern "/health" (handler := fun request => Response.ok.text "ok")
```

## License

This library is released under the Apache 2.0 license. See the LICENSE
file for the complete license text.
