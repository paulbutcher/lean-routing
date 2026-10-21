# lean-routing, on LeanIn

Fork of `paulbutcher/lean-routing` at `f2a7a11` (Apache-2.0; the upstream licence and notices
remain). The fork keeps the typed patterns, links, matching and route-table code and replaces the
**serving layer** with LeanIn.

## What changed

- `Routing.Server` no longer imports `Std.Http.Server`. A `Request` is LeanIn's `H1.Head`, parsed
  `RequestTarget`, streaming `BodyReader`, and `Std.Http.Extensions`; a `Response` is a buffered
  status/reason/headers/body value; handlers run in `LeanIn.Runtime.VM`.
- `StatelessHandler` keeps `onRequest` and `onContinue`. `toStreamHandlerOf` asks `onContinue`
  when the request expects a `100 Continue`; set the LeanIn config's `h1.autoContinue := false` so
  the driver leaves the interim response to that decision.
- `toHandler` is a `LeanIn.Http.Server.StreamHandler`; `serveConnStream` serves it.
- `Result` is `Request → VM Response`, so route handlers now return `pure` responses rather than
  `ContextAsync (Std.Http.Response …)`.
- `Std.Http` remains only for independent data types: `Method`, `Status`, `Header`, `Extensions`,
  `RequestTarget`.

Dependency: `scidonia/leanin @ "v0.4.0"`. Package version is `0.11.0` (the handler/result surface
is a breaking change).

## Tests

`test/RoutingTests/Server.lean` and `Router.lean` build native requests from `H1.parseHead` and run
`toHandler` through `Routing.runRequest`; they check matched-route publication, 404 absence, the
mounted-index redirect and sub-router `onContinue` selection. Pure pattern/link tests are unchanged.

`Routing` (the aggregate) deliberately excludes `Routing.Server` and `Routing.Router`, so the
upstream `leanFree` guarantee still holds for consumers that only need patterns, links and
matching; serving imports LeanIn and its macro frontend explicitly.

A public-socket fixture is `tests/server.sh`, and `bench/README.md` records the paired before/after
run. `toStreamHandler` is the connection adapter; `toHandler` keeps the upstream `StatelessHandler`
meaning. The routing API remains buffered, as upstream's `Result` is; a streaming route API would be
an addition rather than a parity item. `100-continue` is router-controlled when `h1.autoContinue` is false; the socket
fixture checks both the interim and the refusal.
