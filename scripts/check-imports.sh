#!/usr/bin/env bash
# Copyright (c) 2026 Paul Butcher. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The library may reach the Lean package only through `meta import`, which the compiler admits
# for elaboration alone. A plain import would put the frontend back into every consumer's binary,
# and it is an easy thing to write by accident, so it is rejected here off the source text.
# `check-runtime.sh` reads the same claim off what the compiler produced.

set -euo pipefail

cd "$(dirname "$0")/.."

if matches=$(grep -rnE '^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+Lean([.[:space:]]|$)' \
    Routing.lean Routing 2>/dev/null); then
  echo "error: the library must reach the Lean package only via 'meta import':" >&2
  echo "$matches" >&2
  exit 1
fi

echo "ok: the library imports the Lean package only as 'meta import'"
