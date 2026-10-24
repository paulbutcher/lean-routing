#!/usr/bin/env bash
# Copyright (c) 2026 Paul Butcher. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Serves one application on each engine in turn and drives it with wrk over keep-alive loopback
# connections. Each round starts both servers fresh, one after the other, and the order alternates
# between rounds, so drift in the host's load falls on both engines rather than on one.
#
# Settings, from the environment:
#   LEVELS       concurrent connections, one run per level      "1 8 32"
#   ROUNDS       rounds per level                               3
#   DURATION     seconds per measurement                        5
#   TARGET       the path requested (see RoutingBench.targets)  /bench
#   SHAPE        minimal (Host only) or browser (ten headers)   minimal
#   PIPELINE     requests in flight per connection              1
#   SERVER_CPUS  CPUs the server is pinned to (taskset -c)      1
#   CLIENT_CPUS  CPUs wrk is pinned to                          2,3
#   THREADS      wrk threads, capped at the level               2
#   CARRIERS     LeanIn carriers; match SERVER_CPUS             1
#   PORT         where the server listens                       8601

set -euo pipefail

cd "$(dirname "$0")"

LEVELS=${LEVELS:-"1 8 32"}
ROUNDS=${ROUNDS:-3}
DURATION=${DURATION:-5}
TARGET=${TARGET:-/bench}
SHAPE=${SHAPE:-minimal}
PIPELINE=${PIPELINE:-1}
SERVER_CPUS=${SERVER_CPUS:-1}
CLIENT_CPUS=${CLIENT_CPUS:-2,3}
THREADS=${THREADS:-2}
CARRIERS=${CARRIERS:-1}
PORT=${PORT:-8601}

command -v wrk >/dev/null || { echo "error: wrk is needed" >&2; exit 2; }
command -v taskset >/dev/null || { echo "error: taskset is needed" >&2; exit 2; }

lake build benchStd benchLeanIn >/dev/null

headers=()
case "$SHAPE" in
  minimal) ;;
  browser)
    headers=(
      -H "User-Agent: Mozilla/5.0 (X11; Linux aarch64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0 Safari/537.36"
      -H "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
      -H "Accept-Language: en-GB,en;q=0.9"
      -H "Accept-Encoding: gzip, deflate, br"
      -H "Cookie: session=0123456789abcdef0123456789abcdef; theme=dark"
      -H "Referer: http://127.0.0.1/"
      -H "Sec-Fetch-Dest: document"
      -H "Sec-Fetch-Mode: navigate"
      -H "Upgrade-Insecure-Requests: 1")
    ;;
  *) echo "error: SHAPE must be minimal or browser" >&2; exit 2 ;;
esac

listening() { (exec 3<>"/dev/tcp/127.0.0.1/$PORT") 2>/dev/null; }

pid=
stop() {
  if [ -n "$pid" ]; then kill "$pid" 2>/dev/null || true; wait "$pid" 2>/dev/null || true; fi
  pid=
}
rows=$(mktemp)
trap 'stop; rm -f "$rows"' EXIT

start() {
  # A server left over from another run would answer in place of this one.
  if listening; then echo "error: port $PORT is already in use" >&2; exit 2; fi
  case "$1" in
    std) taskset -c "$SERVER_CPUS" .lake/build/bin/benchStd "$PORT" >/dev/null & ;;
    leanin) taskset -c "$SERVER_CPUS" .lake/build/bin/benchLeanIn "$PORT" "$CARRIERS" >/dev/null & ;;
  esac
  pid=$!
  for _ in $(seq 1 200); do listening && return; sleep 0.05; done
  echo "error: the $1 server did not start listening" >&2; exit 2
}

# One measurement: "<requests per second> <p50 µs> <non-2xx/3xx responses>".
measure() {
  local level=$1 threads=$THREADS script=()
  [ "$threads" -gt "$level" ] && threads=$level
  [ "$PIPELINE" -gt 1 ] && script=(-s pipeline.lua -- "$PIPELINE")
  taskset -c "$CLIENT_CPUS" wrk -t "$threads" -c "$level" -d "${DURATION}s" --latency \
      "${headers[@]}" "http://127.0.0.1:$PORT$TARGET" "${script[@]}" |
    awk '
      /^Requests\/sec:/ { rps = $2 }
      /^ +50%/ {
        v = $2; unit = v; sub(/[0-9.]+/, "", unit); sub(/[a-z]+$/, "", v)
        p50 = (unit == "s") ? v * 1e6 : (unit == "ms") ? v * 1e3 : v
      }
      /Non-2xx or 3xx responses:/ { bad = $NF }
      END { printf "%.0f %.0f %d\n", rps, p50, bad }'
}

echo "# $(date -u +%FT%TZ) $(git rev-parse --short HEAD 2>/dev/null || echo unknown)" \
  "load=$(cut -d' ' -f1-3 /proc/loadavg) target=$TARGET shape=$SHAPE pipeline=$PIPELINE" \
  "server_cpus=$SERVER_CPUS client_cpus=$CLIENT_CPUS carriers=$CARRIERS duration=${DURATION}s"
echo "level round engine rps p50us bad"

# In this shell rather than a pipeline's subshell, so that the trap above can stop the server.
for level in $LEVELS; do
  for round in $(seq 1 "$ROUNDS"); do
    order="std leanin"
    [ $((round % 2)) -eq 0 ] && order="leanin std"
    for engine in $order; do
      start "$engine"
      echo "$level $round $engine $(measure "$level")" | tee -a "$rows"
      stop
    done
  done
done

# Per level: each engine's median, and the median of the per-round ratios, which is what pairing
# within a round buys.
echo
echo "level std_rps leanin_rps leanin/std(median of rounds) std_p50us leanin_p50us"
awk '
  function median(a, n,    i, j, t) {
    for (i = 2; i <= n; i++) for (j = i; j > 1 && a[j - 1] > a[j]; j--) { t = a[j]; a[j] = a[j - 1]; a[j - 1] = t }
    return (n % 2) ? a[(n + 1) / 2] : (a[n / 2] + a[n / 2 + 1]) / 2
  }
  $1 ~ /^[0-9]+$/ {
    key = $1 SUBSEP $2
    rps[$3, key] = $4; p50[$3, key] = $5
    if (!($1 in seen)) { seen[$1] = 1; levels[++nl] = $1 }
    rounds[$1] = ($2 > rounds[$1]) ? $2 : rounds[$1]
  }
  END {
    for (l = 1; l <= nl; l++) {
      level = levels[l]; n = 0
      for (r = 1; r <= rounds[level]; r++) {
        key = level SUBSEP r
        if ((("std", key) in rps) && (("leanin", key) in rps) && rps["std", key] > 0) {
          n++
          s[n] = rps["std", key]; i[n] = rps["leanin", key]; q[n] = i[n] / s[n]
          sp[n] = p50["std", key]; ip[n] = p50["leanin", key]
        }
      }
      if (n) printf "%s %.0f %.0f %.2f %.0f %.0f\n", level, median(s, n), median(i, n), median(q, n), median(sp, n), median(ip, n)
    }
  }' "$rows"
