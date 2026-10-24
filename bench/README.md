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

2026-10-24, on the uncommitted working tree over `45fe767`, LeanIn `ffe3a0a`; an aarch64 container with 18 cores (kernel linuxkit). Default settings: `/bench`, one server CPU and one LeanIn carrier, `wrk` with two threads on two other CPUs, three rounds of 5 s per level. The load average was 0.38 before the first run and 4.93 before the second, most of it the benchmark's own server and `wrk`, on CPUs no other work was pinned to.

Requests with only `Host` (`SHAPE=minimal`), medians over the rounds:

| connections | std req/s | leanin req/s | leanin/std | std p50 | leanin p50 |
|---:|---:|---:|---:|---:|---:|
| 1 | 9 075 | 33 809 | 3.68 | 108 µs | 29 µs |
| 8 | 8 614 | 72 206 | 8.38 | 910 µs | 108 µs |
| 32 | 6 909 | 90 040 | 12.92 | 4 580 µs | 344 µs |

Browser-shaped requests, ten headers (`SHAPE=browser`):

| connections | std req/s | leanin req/s | leanin/std | std p50 | leanin p50 |
|---:|---:|---:|---:|---:|---:|
| 1 | 8 560 | 23 761 | 2.79 | 114 µs | 39 µs |
| 8 | 8 197 | 42 489 | 5.18 | 940 µs | 182 µs |
| 32 | 6 586 | 48 804 | 7.41 | 4 830 µs | 645 µs |

In memory (`benchDispatch 100000`), nanoseconds per request:

| target | exercises | match | std | leanin |
|---|---|---:|---:|---:|
| `/bench` | literal | 137 | 1 290 | 907 |
| `/users/7` | capture | 226 | 1 473 | 965 |
| `/items/63` | 64 literals | 201 | 1 398 | 869 |
| `/blog` | slash redirect | 93 | 1 156 | 689 |
| `/nope` | miss | 89 | 1 089 | 492 |

- Routing is not where the time goes on either engine: a request costs LeanIn about 11 µs at 32 connections and `Std.Http.Server` about 145 µs, against at most a quarter of a microsecond to match it and about one to run the handler.
- `Std.Http.Server` serves fewer requests as connections rise, while LeanIn serves more, so the ratio grows with concurrency.
- Ten headers cost LeanIn about 9 µs a request at 32 connections, close to the microsecond a header its conversion to `Std.Http` headers is measured at in LeanIn's own `docs/PERFORMANCE.md`. That conversion is the price of the `Std.Http` types every engine shares here, and it narrows the gap for browser traffic to 2.8–7.4×.
