# Routing

A typed HTTP router for Lean 4, over [`Std.Http`](https://leanprover-community.github.io/mathlib4_docs/Std/Http.html)'s request and response types, served by `Std.Http.Server` or by [LeanIn](https://github.com/scidonia/leanin) (see [Engines](#engines)). Route patterns like `"/users/:id:Nat"` determine the exact type your handler must have; a wrong-arity or wrong-type handler is a compile error, not a runtime bug.

See: [Formally verified CRUD](https://paulbutcher.com/lean2.html).

## Installation

Add an engine to your `lakefile.toml`; it requires `routing` itself:

```toml
[[require]]
name = "routing-std"
git = "https://github.com/paulbutcher/lean-routing.git"
subDir = "std"
```

For LeanIn, `name = "routing-leanin"` and `subDir = "leanin"`. A library that only declares routes and links, or writes handlers for any engine, can require `routing` alone.

## Usage

### 1. Declare your routes

```lean
import Routing

route_table AppName
  [ index := "/",
    user := "/users/:id:Nat",
    userPost := "/users/:id:Nat/posts/:slug:String" ]
```

This is a macro which parses the route specifications and generates `AppName.patterns` (the parsed patterns, for step 2) and `AppName.links` (link-building functions, described below).

### 2. Combine route handlers into an application

```lean
import RoutingStd

open Std Http Server
open Routing
open AppName

def app : StatelessHandler .std := [
    .get patterns.index (fun request => Response.ok.text "home"),
    .get patterns.user (fun (id : Nat) request => Response.ok.text s!"user #{id}"),
    .post patterns.userPost (fun (id : Nat) (slug : String) request => Response.ok.text s!"user #{id}, post {slug}")
  ] |> toHandler
```

Unmatched requests get a default `404 Not Found`; pass `notFound := ...` to `toHandler` to override it.

A route that an earlier one with the same method always beats is a compile error naming both: `/users/new` after `/users/:name:String`, say, or `/users/` after `/users`, which answers the link `/users/` as `/users` with a trailing slash. `Router.toHandler` checks routes in the order a router tries them, so it also rejects one behind an earlier router's mount root, or behind the slash redirect an earlier router gives a mounted index. The check runs with `native_decide`, so its proof trusts the compiler and carries an axiom of its own; pass `(by routes_unshadowed +kernel)` as the proof instead (`h := …` for `toHandler`, whose second argument is `notFound`) to keep to the standard axioms, at a cost of about a second for 200 routes. Unlike `decide +kernel`, it proves a table whose handlers mention a local value, such as a library's handlers over an engine its application chooses. A table whose methods or patterns are only known at run time cannot be checked while compiling: build it with `RouteIndex.ofChecked` and serve it with `RouteIndex.toHandler`, or use `Router.toHandlerChecked`, each of which returns the same report as an error. A table defined in another module must be `@[expose]`d for its handlers to close over local values.

### 3. Wire into a server

A `StatelessHandler .std` is a `Std.Http.Server.Handler`, so it is served as it is:

```lean
def main : IO Unit := do
  let addr : Net.SocketAddress := .v4 { addr := Net.IPv4Addr.ofParts 127 0 0 1, port := 8080 }
  let _ ← Async.toIO (Server.serve addr app)
  ...
```

On LeanIn, `app.toLeanIn` is the `StdHandler` that `LeanIn.Http.Server.serveConnStd` serves; [bench/RoutingBench/ServeLeanIn.lean](bench/RoutingBench/ServeLeanIn.lean) is a complete server.

### Generating links

Use `AppName.links.<name>` anywhere you need a URL for one of your routes, e.g. in a template:

```lean
#eval AppName.links.index       -- "/"
#eval AppName.links.user 42     -- "/users/42"
```

`AppName.links.user` is a function (`Nat → String`) because its pattern has one capture; a pattern with no captures gives a plain `String`. Literal segments and `String` captures are percent-encoded, so `AppName.links.userPost 1 "a b/c"` is `"/users/1/posts/a%20b%2Fc"`, which dispatches back to `"a b/c"`. A `Nat` capture matches only the digits a link renders, so `/users/042` is not a second path to user 42. A link whose first segment is empty starts with `/./`, since one starting with `//` would name another host. No link can carry an empty, `.` or `..` segment, so a pattern cannot contain a `.` or `..` literal (`PathSeg.lit` requires a proof, and `PathSeg.lit?` checks a runtime string) and a `String` capture never matches any of the three; validate such values (usernames, say) where they are created.

### Hierarchical routes

A `route_table` can `mount` another `route_table`-generated table under a literal path prefix, nesting its whole `patterns`/`links` shape:

```lean
route_table Blog
  [ index := "/",
    post  := "/:slug:String" ]

route_table AppName
  [ index := "/",
    blog  := mount "/blog" Blog ]
```

```lean
#eval AppName.links.blog.index        -- "/blog/"
#eval AppName.links.blog.post "hi"    -- "/blog/hi"
```

`AppName.patterns.blog.post` is the full prefixed pattern, so it plugs into `Route.get`/etc. the same way any other pattern does, and a handler for it needs no special wrapping: a mount prefix must be literal (no `:name:Kind` captures), so it never changes a route's required handler type. Mounts nest to any depth: a table that itself mounts other tables can be mounted again further up.

A mounted index renders with a trailing slash, as the unmounted index `/` has, so that relative links from it work (see "Relative links" below). A request for it without the slash gets a `308` redirect to the slashed form.

### Hierarchical handlers

`mount_routes "prefix" routes` is the handler-level counterpart: it takes a `List (Route _)` built against a sub-app's own *unprefixed* patterns and re-targets it under a literal prefix, so a module's handlers can be written once and mounted anywhere:

```lean
def blogRoutes : List (Route (Result .std)) :=
  [ .get Blog.patterns.index (fun request => Response.ok.text "blog home"),
    .get Blog.patterns.post (fun (slug : String) request => Response.ok.text s!"post {slug}") ]

def app : StatelessHandler .std :=
  ( [ .get AppName.patterns.index (fun request => Response.ok.text "home") ] ++
    mount_routes "/blog" blogRoutes
  ) |> toHandler
```

Like `mount`, no handler wrapping is needed for the prefix. Unlike `mount`, nesting is just repeated `mount_routes` + `++`; routes are already a flat list, so there's no structure to walk.

### Routers and middleware

A `Router` groups routes behind its own middleware, so different parts of an application can sit behind different stacks. A middleware is any `StatelessHandler e → StatelessHandler e`. One written against `Std.Http.Server.StatelessHandler`, such as those in [lean-middleware](https://github.com/paulbutcher/lean-middleware), runs on `.std` as `fun h => .ofStd (mw h.toStd)`. a router applies its list in order, the first outermost, once when `Router.toHandler` builds it.

```lean
def api : Router .std :=
  { middlewares := [requireToken],
    routes := [ .mount AppName.patterns.blog
      [ .get Blog.patterns.index (fun request => Response.ok.text "blog home"),
        .get Blog.patterns.post (fun (slug : String) request => Response.ok.text s!"post {slug}") ] ],
    fallback := some blogNotFound }

def site : Router .std :=
  { middlewares := [logging],
    routes := [ .get AppName.patterns.index (fun request => Response.ok.text "home") ],
    routers := [api] }

def app : StatelessHandler .std := site.toHandler
```

A mount takes every request under its root, and its entries are written against the mounted table's own unprefixed `patterns`. Its root is a table's `patterns` value, which records where that table is mounted (`AppName.patterns.blog.mountedAt.segs = ["blog"]`, and `AppName.links.blog.mountedAt = "/blog"`), or a `MountPoint` no table describes. Like a pattern, a root cannot hold a `.` or `..` segment: a literal one such as `.mk ["admin"]` is checked at compile time, and one built at run time comes from `MountPoint.ofSegs? ["t", tenant]`, which returns `none` for an invalid segment. Mounts nest, each root prefixed by those enclosing it.

A router serves a request with its first route that matches, else its first sub-router that takes it, else its `fallback` (a plain `404 Not Found` by default). A router takes a request if one of its routes matches it or one of its mounts or sub-routers takes it, so a miss under `/blog` above gets `blogNotFound`, behind `requireToken`. `matchedRoute?` reports the full pattern, mount roots included, whichever router served the request. As with `toHandler`, a mounted index requested without its slash gets a `308`.

`mountedAt` is reserved as a `route_table` row name, and is an extra field of every generated `Patterns` and `Links` structure, so code building one positionally needs updating.

### Which route matched?

The matched route is stored in the `extensions` of both the request and the response. Read it back with `Routing.matchedRoute?`:

```lean
def handler (request : Request Body.Stream) : ContextAsync (Response Body.Any) := do
  let response ← inner request
  match Routing.matchedRoute? response.extensions with
  | some matched => ...   -- matched.segs = [.lit "users", .capture "id" .nat]
  | none => ...           -- nothing matched; this is the 404
```

Alternatively, `Routing.matchedPattern?` drops each capture's kind (useful for telemetry):

```lean
#eval Routing.matchedPattern? response.extensions  -- some "/users/:id", not "/users/:id:Nat"
```

### Relative links

`Routing.relativeUrl current to` builds a relative reference between two already-rendered links, so code inside a module can self-link using its own *unprefixed* `.links`, with no need to know whether, or under what prefix, the module ends up mounted:

```lean
#eval Routing.relativeUrl Blog.links.index (Blog.links.post "hi")  -- "hi"
```

This comes out the same whichever prefix `Blog` is mounted under (or none at all), because a prefix shared by both endpoints cancels out of the computation:

```lean
#eval Routing.relativeUrl AppName.links.blog.index (AppName.links.blog.post "hi")  -- "hi", too
```

Linking to a strict descendant of the current page needs its own segment repeated (`relativeUrl "/posts/5" "/posts/5/edit" = "5/edit"`, not `"edit"`); that is the standard RFC 3986 rule that treats the current page's last segment as a "file", not a directory. Linking *up* to an ancestor page renders as a directory reference (`"."`/`".."`), which resolves to a trailing-slash URL; `dispatch` tolerates that trailing slash once a pattern is otherwise fully matched, so the link still reaches its target.

## Engines

An `Engine` (`Routing/Engine.lean`) is what the router needs of a server: the monad handlers run in, the one its hooks run in, and its request and response body types. Requests and responses are `Std.Http`'s on every engine, so a handler reads `request.line.uri` and sets `response.line.headers` the same way on both.

| Package | Engine | A handler returns | Needs |
|---|---|---|---|
| `routing-std` ([std/](std/)) | `.std` | `ContextAsync (Response Body.Any)`, as for `Std.Http.Server` | nothing beyond Lean |
| `routing-leanin` ([leanin/](leanin/)) | `.leanin` | `LeanIn.Runtime.VM (Response LeanIn.Http.ResponseBody)` | libuv, and LeanIn's `main` until a release carries its `StdHandler` |

Code written for either engine takes `{e : Engine}` and builds a body with `e.text`, as [bench/RoutingBench/App.lean](bench/RoutingBench/App.lean) does. A handler or middleware that needs more of its engine, as one shipped in a library does, takes `{e : Engine} [ServerEngine e]` (`Routing/ServerEngine.lean`), which both engine packages provide:

- `readBody body maximum`: the whole request body, failing once it passes `maximum` bytes; `readText` decodes it as UTF-8.
- `replaceBody body bytes`: a body reading as `bytes` and otherwise as `body` was, for a middleware that reads the body and hands one on.
- `bytes builder content`: a response with that body, and the content type `builder` sets; `html`, `empty` and `e.text` are built from it, so both engines answer them alike.
- Lifts of `IO` into the handler and hook monads, of the hook monad into the handler's, so that a middleware can call `onFailure`, and `MonadExcept IO.Error` and `MonadFinally` for the handler's.

A `catchAll` written this way sees different failures on each engine: LeanIn ends a request whose connection fails without raising an error a handler could catch, and tells `onFailure` itself. [leanin/test/RoutingLeanInTests/ServerEngine.lean](leanin/test/RoutingLeanInTests/ServerEngine.lean) is a router and two middlewares written this way.

`routing` and `routing-std` keep the guarantee that the Lean package stays out of a consumer's binary; `routing-leanin` cannot, because LeanIn imports it. LeanIn's `serveConnStd` requires `continuePolicy := .application`, so that `onContinue` decides, and does not report a stall before the request head, or a head its parser rejects, to `onFailure`.

Moving from 0.12 to `routing-std`: require it, import `RoutingStd`, and write `Result .std`, `StatelessHandler .std`, `Router .std` and `Entry .std` where the unparameterised names were. `Handler.ofFn` becomes `StatelessHandler.ofFn`. Handler bodies are unchanged.

[bench/](bench/README.md) measures the two engines serving one application.

## Formal verification

- Pattern round trip ([test/RoutingTests/Pattern.lean](test/RoutingTests/Pattern.lean), `parsePattern_renderPattern`): rendering a list of well-formed segments to a pattern string and parsing it back recovers exactly those segments.
- Link round trip ([test/RoutingTests/RoundTrip.lean](test/RoutingTests/RoundTrip.lean), `requestSegments_linkFor`): `Std.Http` parses and decodes a link that `linkFor` builds. Dispatching the result against the link's own route calls the handler with the link's values. It assumes `ReadsBack`, a property of `Std.Http`'s parser and decoder fuzzed below, and leaves out the route `[.lit ""]`, whose link `/` reads back as no segments. In a table, an earlier route can still match the link first.
- One path per number ([test/RoutingTests/RoundTrip.lean](test/RoutingTests/RoundTrip.lean), `parseNat?_toString`, `toString_of_parseNat?`): a `Nat` capture matches exactly the digits `toString` prints.
- Links stay on the host ([test/RoutingTests/Host.lean](test/RoutingTests/Host.lean), `resolvedHost_linkFor`, `resolvedHost_mountLink`, `resolvedHost_slashLocation`): from any page, no link, mount link or slash redirect names another host. That includes one whose first segment is empty. `resolvedHost` models RFC 3986's reference resolution as the WHATWG URL standard applies it, so `\` reads as `/` and it drops tabs and newlines. The redirect theorem covers the target before `Header.Value.ofString?` trims it.
- Template stability ([test/RoutingTests/Pattern.lean](test/RoutingTests/Pattern.lean), `renderTemplate_kind_invariant`): changing a capture's kind leaves the endpoint template that `matchedPattern?` reports unchanged, so telemetry grouped by route survives `:id:Nat` becoming `:id:String`.
- Router mounts ([test/RoutingTests/Router.lean](test/RoutingTests/Router.lean), `Route.under_segs`): a route under a `Router` mount has exactly the pattern a `route_table` mount gives it, so it matches what the table's links point at.
- Route trie ([test/RoutingTests/Trie.lean](test/RoutingTests/Trie.lean), `RouteIndex.matchTable_eq`, `RouteIndex.memory_of`): `RouteIndex.matchTable`, which `respond?`, `wantsSlash` and `slashRedirect?` match with, finds the route `matchTable` finds on the index's table, for every index, method and path. The trie holds at most one node per pattern segment, plus the root, and each route's index once.
- Shadowed routes ([test/RoutingTests/Shadow.lean](test/RoutingTests/Shadow.lean), `Route.tryDispatch_of_covers`, `Route.redirect_takes`, `root_takes`, `Internal.reachable_of_unshadowed`): no link reaches a route the check reports, since the route, redirect or mount root reported ahead of it takes every path a link to it gives. Conversely every route it passes has a link path that reaches it past everything tried before, so no route is hidden by several together.
- Router order ([test/RoutingTests/Served.lean](test/RoutingTests/Served.lean), `compile_served`, `Router.serves_link`): a router serves a request with the first of `Router.takers` that takes it, so every route a router passes the check with is the one it serves some link to that route with. Both are stated over `Internal.Compiled.served`, which makes the same choice as the handler built beside it, before any middleware.
- Mount-prefix cancellation ([test/RoutingTests/RelativeLink.lean](test/RoutingTests/RelativeLink.lean), `relativeSegments_prefix`): a prefix shared by both endpoints drops out of a relative link, so a module's self-links are the same wherever it is mounted.
- By construction: a handler's type is computed from its pattern, so a wrong-arity or wrong-type handler fails to compile, and `PathSeg.lit` and `MountPoint` take a proof that no segment is `.` or `..`. The `#guard_msgs` tests in [test/RoutingTests/](test/RoutingTests/) pin these, along with the compile-time rejection of malformed patterns, duplicate route names and captured mount prefixes.

## Conformance tests

There is no external suite for a router, so these check behaviour against the specifications and implementation it sits between.

- [test/RoutingTests/Handler.lean](test/RoutingTests/Handler.lean): links are parsed and percent-decoded by `Std.Http`'s own request-target parser, as `toHandler` does, and must dispatch back to the values they were built from, including literals holding `#`, `?` and `%`; an empty, `.` or `..` `String` capture never matches.
- [test/RoutingTests/RelativeLink.lean](test/RoutingTests/RelativeLink.lean): the RFC 3986 edge cases, that a same-page link is not the empty same-document reference, that a first segment holding `:` is not read as a scheme nor an empty one as an absolute path, and that an upward `"."` link resolves to a trailing-slash path `dispatch` still serves.
- [test/RoutingTests/Server.lean](test/RoutingTests/Server.lean): the real `toHandler` against a real `Std.Http` request, checking that the matched route reaches both the request's and the response's `extensions`, that a 404 carries none, and that a mounted index requested without its slash gets a `308` with the query intact.
- [test/RoutingTests/Router.lean](test/RoutingTests/Router.lean): a `Router` tree against real requests, checking middleware order, which router serves a hit and which answers a miss under a mount, the full pattern reported on both request and response, and that `Expect: 100-continue` is decided by the router that would serve the request.
- [test/RoutingTests/Engine.lean](test/RoutingTests/Engine.lean): the core on an engine with no server behind it, checking the `404` and the slash redirect, the two responses it builds through `Engine.text`.
- [leanin/test/RoutingLeanInTests/Engines.lean](leanin/test/RoutingLeanInTests/Engines.lean): one route table, middleware and `Router`, written once, against both engines, checking each answers every request, and every continue, as the other does.

## Property-based testing

- [test/RoutingTests/Handler.lean](test/RoutingTests/Handler.lean): [Plausible](https://github.com/leanprover-community/plausible) fuzzing, weighted towards `.`, `/`, `%`, `?`, `#`, `:` and space, of the link round trip through `Std.Http`'s encoder and decoder: dispatching the served form of a generated link recovers its `String` capture, or nothing when the capture is unlinkable. It also fuzzes `ReadsBack`, the property of `Std.Http` that the proved link round trip assumes. Properties rather than theorems because those functions have no lemmas relating them.
- [test/RoutingTests/RelativeLink.lean](test/RoutingTests/RelativeLink.lean): fuzzing `relativeUrl` against a model of RFC 3986 §5.2 resolution, that the reference it returns resolves back to its target, or to the target with a trailing slash, which `dispatch` accepts.

## License

This library is released under the Apache 2.0 license. See the LICENSE file for the complete license text.
