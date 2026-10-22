# lean-routing, on LeanIn

Fork of `paulbutcher/lean-routing` at `f2a7a11` (Apache-2.0; the upstream licence and notices
remain). The fork keeps the typed patterns, links, matching and route-table code and replaces the
**serving layer** with LeanIn.

## What changed

- `Routing.Server` no longer imports `Std.Http.Server`. A `RequestM Body` carries a
  `Std.Http.Request.Head`, a body of the host's type, and `Std.Http.Extensions`; `Request` aliases
  LeanIn's `BodyReader`. A `Response` remains a buffered status/reason/headers/body value.
- `ResultM m ReqBody` and `StatelessHandlerM m ReqBody` parameterize the computation and request
  body. `Result` and `StatelessHandler` remain the native `VM`/`BodyReader` aliases, so existing
  route declarations are unchanged.
- `toStreamHandlerOf` converts the parsed H1 head to `Std.Http.Request.Head` at dispatch and asks
  `onContinue` with that shared line. Set the LeanIn config's `h1.autoContinue := false` so the
  driver leaves the interim response to the decision.
- `toHandlerM`, `runRequestM` and `respond?M` are the generic dispatch path; the native names are
  aliases. `Routing.Stock.toStatelessHandler` instantiates the same route source at
  `ContextAsync`/`Body.Stream` and converts the buffered response to `Std.Http.Response Body.Any`.
- `Std.Http` remains the metadata surface: `Method`, `Status`, `Header`, `Extensions`,
  `RequestTarget` and now `Request.Head`.
- The streaming extension (`Routing.Streaming`) remains native and uses the same converted line.

Dependency: `scidonia/leanin @ "028ca6a"`. Package version is `0.11.0` (the handler/result surface
is a breaking change).

## Tests

`test/RoutingTests/Server.lean` and `Router.lean` build native requests from `H1.parseHead`, convert
the line once, and run `toHandler` through `Routing.runRequest`; they check matched-route
publication, 404 absence, the mounted-index redirect and sub-router `onContinue` selection.
`test/RoutingTests/Generic.lean` compiles one route declaration at both `Result` and
`Stock.Result`, and runs both handlers for `/hello`; it checks status, body and the shared
`x-contract` header. `Routing.withRouteHeader` adds the matched template as `x-route` on both
hosts. Pure pattern/link tests are unchanged.

`Routing` (the aggregate) deliberately excludes `Routing.Server` and `Routing.Router`, so the
upstream `leanFree` guarantee still holds for consumers that only need patterns, links and
matching; serving imports LeanIn and its macro frontend explicitly.

A public-socket fixture is `tests/server.sh`, and `bench/README.md` records the paired before/after
run. `toStreamHandler` is the connection adapter; `toHandler` keeps the upstream `StatelessHandler`
meaning. The routing API remains buffered, as upstream's `Result` is; a streaming route API would be
an addition rather than a parity item. `100-continue` is router-controlled when `h1.autoContinue` is false; the socket
fixture checks both the interim and the refusal.
