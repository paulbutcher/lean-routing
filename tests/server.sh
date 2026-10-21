#!/usr/bin/env bash
# server.sh — the routing library on LeanIn at the public socket.
set -uo pipefail
cd "$(dirname "$0")/.."
lake build routingServer >/dev/null || { echo "server: build failed" >&2; exit 1; }
port="${ROUTING_PORT:-8511}"
./.lake/build/bin/routingServer "$port" >/tmp/routing-server.log 2>&1 &
pid=$!
trap 'kill $pid 2>/dev/null; wait $pid 2>/dev/null' EXIT
for _ in $(seq 1 100); do
  ss -ltn 2>/dev/null | grep -q ":${port} " && break
  sleep 0.05
done
check() {
  local out status body
  out=$(curl -s -m 5 -w $'\n%{http_code}' "http://127.0.0.1:${port}$1")
  status=${out##*$'\n'}; body=${out%$'\n'*}
  [ "$status" = "$2" ] && [ "$body" = "$3" ] || {
    echo "server: $1 -> $status [$body], expected $2 [$3]" >&2; exit 1; }
}
check /bench 200 hello
check /users/7 200 "user 7"
check /blog 200 blog
check /nope 404 "Not Found"
echo "server: all checks passed"
