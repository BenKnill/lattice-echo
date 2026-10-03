#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
exec > >(tee validation/local-checks.log) 2>&1
export OMP_NUM_THREADS=1 NUMBA_NUM_THREADS=1 MKL_NUM_THREADS=1
run() {
  printf '$'
  printf ' %q' "$@"
  printf '\n'
  "$@"
}
run date -u +%Y-%m-%dT%H:%M:%SZ
run git rev-parse HEAD
run sha256sum docs/live.html docs/live.css docs/live.js docs/live-guide.html docs/lattice.js tests/live-controls.mjs tests/live-models.mjs
run node --check docs/live.js
run git diff --check
run taskset -c 11 node tests/live-models.mjs
run taskset -c 11 node tests/live-controls.mjs
printf 'Local validation completed successfully. Browser rendering is tested separately in the offline kit.\n'
