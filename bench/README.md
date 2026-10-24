# Engine benchmark

One application, [RoutingBench/App.lean](RoutingBench/App.lean), written once and served by each engine: a literal route, a typed capture, a mounted index and its slash redirect, a miss, 64 literal routes for the trie to skip, and one middleware layer. Nothing here is shipped; it needs libuv and `wrk`, which the devcontainer provides.

## In memory

```
lake build benchDispatch && .lake/build/bin/benchDispatch 100000
```

For each path in `RoutingBench.targets`, nanoseconds per request: `matchNs` is dispatch alone, with no engine; `stdNs` and `leaninNs` run the whole handler, middleware included, on each engine. The gap between `matchNs` and an engine's figure is that engine's cost of running a handler and building its response. LeanIn's conversion from its parsed head to `Std.Http`'s happens at the socket, so it is in the socket figures only.

## At the socket

```
bench/run.sh
```

Each round starts both servers fresh, one after the other, alternating which goes first, and drives each with `wrk` over keep-alive loopback connections, server and client pinned to separate CPUs. It prints one row per measurement, then per level each engine's median requests per second and p50 latency, and the median over rounds of the LeanIn/Std ratio. The settings, from the environment, are listed at the top of [run.sh](run.sh); the ones worth varying are `LEVELS`, `SHAPE=browser` (ten headers, which LeanIn validates into `Std.Http` headers at about a microsecond each), `PIPELINE` and `TARGET`. Give LeanIn as many `CARRIERS` as `SERVER_CPUS` names, so that both engines have the same CPUs.

Record the commit, host and load average the script prints alongside any result kept here.

## Results

2026-10-24, at `146f2d6` with LeanIn `ffe3a0a`, on an aarch64 container with 18 cores (kernel linuxkit), with other work on the host shut down. Default settings: `/bench`, one server CPU and one LeanIn carrier, `wrk` with two threads on two other CPUs, three rounds of 5 s per level. Each run started with the load average below 0.5.

Requests with only `Host` (`SHAPE=minimal`), medians over the rounds:

| connections | std req/s | leanin req/s | leanin/std | std p50 | leanin p50 |
|---:|---:|---:|---:|---:|---:|
| 1 | 9 463 | 33 679 | 3.59 | 103 µs | 29 µs |
| 8 | 9 186 | 71 326 | 7.76 | 848 µs | 109 µs |
| 32 | 6 980 | 90 442 | 13.17 | 4 520 µs | 345 µs |

Browser-shaped requests, ten headers (`SHAPE=browser`):

| connections | std req/s | leanin req/s | leanin/std | std p50 | leanin p50 |
|---:|---:|---:|---:|---:|---:|
| 1 | 8 353 | 23 406 | 2.76 | 116 µs | 40 µs |
| 8 | 8 076 | 42 498 | 5.11 | 950 µs | 182 µs |
| 32 | 6 619 | 47 847 | 7.20 | 4 780 µs | 652 µs |

In memory (`benchDispatch 100000`), nanoseconds per request, the median of three runs:

| target | exercises | match | std | leanin |
|---|---|---:|---:|---:|
| `/bench` | literal | 136 | 1 291 | 898 |
| `/users/7` | capture | 224 | 1 477 | 960 |
| `/items/63` | 64 literals | 199 | 1 401 | 867 |
| `/blog` | slash redirect | 93 | 1 158 | 685 |
| `/nope` | miss | 88 | 1 089 | 488 |

- Routing is not where the time goes on either engine: a request costs LeanIn about 11 µs at 32 connections and `Std.Http.Server` about 143 µs, against at most a quarter of a microsecond to match it and about one to run the handler.
- `Std.Http.Server` serves fewer requests as connections rise, while LeanIn serves more, so the ratio grows with concurrency.
- Ten headers cost LeanIn about 10 µs a request at 32 connections, close to the microsecond a header its conversion to `Std.Http` headers is measured at in LeanIn's own `docs/PERFORMANCE.md`. That conversion is the price of the `Std.Http` types every engine shares here, and it narrows the gap for browser traffic to 2.8–7.2×.
