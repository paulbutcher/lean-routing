# Before/after routing benchmark

The two arms serve the same routes and response bytes (`/bench` -> `hello`,
`/users/:id` -> `user {id}`, `/blog` -> `blog`), on the same host and client.

## Native arm (this branch)

```bash
lake build routingServer
./.lake/build/bin/routingServer 8520
```

## Upstream arm

Check out `paulbutcher/lean-routing @ f2a7a11`, copy
`bench/upstream/Server.lean` to `Examples/Server.lean`, and add:

```lean
lean_exe upstreamServer where
  root := `Examples.Server
```

to its `lakefile.lean`; then `lake build upstreamServer` and run it on 8521.
That arm uses `Routing.toHandler` on `Std.Http.Server`; the native arm uses it on
`LeanIn.Http.Server.serveConnStream`.

## Drive

`load.mjs` is LeanIn's keep-alive client, copied here so the measurement is self-contained.

```bash
node bench/load.mjs 8521 1 5 /bench
LOAD_PIPE=16 node bench/load.mjs 8521 1 5 /bench
```

## Result (2026-10-21)

Paired, alternating order, 3 rounds, 5 s per arm, client pinned to CPU 2. Host load average was not
recorded, so this is provisional, not a performance record.

| depth | C | upstream rps | native rps | native / upstream |
|---|---:|---:|---:|---:|
| 1 | 1 | 946–971 | 13 555–13 689 | 14.1–14.3× |
| 1 | 8 | 1 379–1 630 | 18 595–25 367 | 13.4–15.6× |
| 1 | 32 | 1 349–1 477 | 26 917–28 453 | 18.7–21.1× |
| 16 | 1 | 1 497–1 612 | 12 955–13 914 | 8.2–9.3× |
| 16 | 8 | 2 847–2 973 | 25 367–26 830 | 8.6–9.1× |
| 16 | 32 | 2 861–2 977 | 28 882–31 538 | 10.1–10.6× |

The upstream arm's p50 is ~0.9 ms at C=1 and ~4.6 ms at C=8, so its low absolute rate is the
Std.Http/stock-async serving path, not a routing-dispatch effect. This is a **stack** comparison:
the router's own matching cost must be measured separately in memory.

## Dispatch cost

`dispatchBench` isolates the router from the socket stack: `parseNs` is one
`Std.Http.RequestTarget.parse?`, `matchNs` one `matchTable` over 64 routes, and
`runNs` one full `runRequest` including VM execution of a pure handler.

```
dispatch|n=200000|parseNs=3|matchNs=2|runNs=796
```

The parse/match figures are at the timer/optimizer resolution floor and should
be treated as "small", not exact. The handler run is ~0.8 µs; the server path is
~77 µs/request at 13k rps, so routing dispatch is roughly 1% of the serving
cost. The remaining cost is the LeanIn HTTP/VM bridge and response path, not
route matching.
