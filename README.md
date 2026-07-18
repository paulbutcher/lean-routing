# Routing

A typed HTTP router for Lean 4 / [`Std.Http`](https://leanprover-community.github.io/mathlib4_docs/Std/Http.html). Route
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
import Routing

routeTable! AppName
  [ index := "/",
    user := "/users/:id:Nat",
    userPost := "/users/:id:Nat/posts/:slug:String" ]
```

This is a macro which parses the route specifications and generates `AppName.patterns` (the parsed patterns, for step 2) and `AppName.links` (link-building functions — see below).

### 2. Combine route handlers into an application

```lean
import Std.Http.Server
import Routing

open Std Http Server
open Routing
open AppName

def app : StatelessHandler := [
    .get patterns.index (fun request => Response.ok.text "home"),
    .get patterns.user (fun (id : Nat) request => Response.ok.text s!"user #{id}"),
    .post patterns.userPost (fun (id : Nat) (slug : String) request => Response.ok.text s!"user #{id}, post {slug}")
  ] |> toHandler
```

Unmatched requests get a default `404 Not Found`; pass `notFound := ...` to `toHandler` to
override it.

### 3. Wire into a server

```lean
def main : IO Unit := do
  ... Std.Http.Server.run app ...
```

### Generating links

Use `AppName.links.<name>` anywhere you need a URL for one of your routes, e.g. in a template:

```lean
#eval AppName.links.index       -- "/"
#eval AppName.links.user 42     -- "/users/42"
```

`AppName.links.user` is a function (`Nat → String`) because its pattern has one capture; a
pattern with no captures gives a plain `String`.

## License

This library is released under the Apache 2.0 license. See the LICENSE
file for the complete license text.
