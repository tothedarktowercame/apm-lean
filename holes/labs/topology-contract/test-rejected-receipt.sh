#!/usr/bin/env bash
# Exercise the real dispatch, extraction, transition and main-loop code, with
# only Agency I/O and live repository/seat setup replaced in an isolated copy.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
export TEST_HERE="$HERE" TOPOLOGY_NO_NOTIFY=1
python3 - "$HERE/topology-build-loop.sh" "$scratch/loop.sh" <<'PY'
from pathlib import Path
import sys
source = Path(sys.argv[1]).read_text()
source = source.replace('HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"',
                        'HERE="$TEST_HERE"')
start = source.index('if [ "$MODE" = replay ]; then')
end = source.index('i=0\nSTALL_KEY=', start)
# Keep the actual main loop and apply_job_result. No mocked build_step or ledger.
setup = r'''
ROOT="$TEST_ROOT"
repository_safe() { :; }
send_notice() { :; }
python3() {
  local n=0
  [ ! -f "$RUNS/dispatched" ] || n="$(cat "$RUNS/dispatched")"
  n=$((n+1))
  cat > "$RUNS/prompt-$n"
  printf '%s\n' "$n" > "$RUNS/dispatched"
  printf '{"job-id":"test-%s"}\n' "$n"
}
wait_job() {
  local n token fixture
  LAST_JOB="$1"
  n="${LAST_JOB#test-}"
  token="$(bb "$HERE/inflight.bb" field "$INFLIGHT" token)"
  fixture=go-receipt.edn
  if [ "$TEST_OUTCOME" = valid ] && [ "$n" -gt 1 ]; then
    fixture=stop-receipt.edn
  fi
  mkdir -p "$RUNS/jobs"
  LAST_RESULT="$RUNS/jobs/$LAST_JOB.result.txt"
  printf 'TOPOLOGY_RECEIPT_EDN %s %s\n' "$token" "$(tr '\n' ' ' < "$HERE/fixtures/$fixture")" > "$LAST_RESULT"
}
'''
Path(sys.argv[2]).write_text(source[:start] + setup + source[end:])
PY

prepare() {
  export TEST_ROOT="$scratch/$1" TOPOLOGY_RUNS="$scratch/$1/runs"
  export TOPOLOGY_LEDGER="$TEST_ROOT/worklist.edn"
  mkdir -p "$TEST_ROOT"
  cp "$HERE/fixtures/checkpoint-ledger.edn" "$TOPOLOGY_LEDGER"
  git -C "$TEST_ROOT" init -q
  git -C "$TEST_ROOT" config user.name 'Topology test'
  git -C "$TEST_ROOT" config user.email 'topology-test@example.invalid'
  git -C "$TEST_ROOT" add worklist.edn
  git -C "$TEST_ROOT" commit -qm initial
}

prepare retry-valid
export TEST_OUTCOME=valid
MAX_ITER=3 bash "$scratch/loop.sh" --once > "$scratch/valid.log" 2>&1
[ "$(cat "$TOPOLOGY_RUNS/dispatched")" = 2 ]
[ "$(bb "$HERE/build_step.bb" unreviewed "$TOPOLOGY_LEDGER")" = checkpoint ]
[ ! -e "$TOPOLOGY_RUNS/inflight.edn" ]
[ ! -e "$TOPOLOGY_RUNS/last-rejected-receipt.json" ]
[ -s "$TOPOLOGY_RUNS/jobs/test-1.receipt.edn" ]
grep -q 'REJECTED receipt from test-1 for checkpoint:' "$scratch/valid.log"
grep -q 'Your previous receipt for this row was rejected:' "$TOPOLOGY_RUNS/prompt-2"
grep -q 'execute at least one relevant verification command during THIS invocation' "$TOPOLOGY_RUNS/prompt-2"
grep -q 'parse the exact map after the nonce with clojure.edn/read-string' "$TOPOLOGY_RUNS/prompt-2"
first_nonce="$(sed -n 's/^TOPOLOGY_RECEIPT_EDN \([^ ]*\).*/\1/p' "$TOPOLOGY_RUNS/prompt-1")"
second_nonce="$(sed -n 's/^TOPOLOGY_RECEIPT_EDN \([^ ]*\).*/\1/p' "$TOPOLOGY_RUNS/prompt-2")"
[ -n "$first_nonce" ] && [ "$first_nonce" != "$second_nonce" ]
[ "$(git -C "$TEST_ROOT" rev-list --count HEAD)" = 2 ]

prepare retry-rejected
export TEST_OUTCOME=rejected
before="$(sha256sum "$TOPOLOGY_LEDGER")"
if MAX_ITER=3 bash "$scratch/loop.sh" > "$scratch/rejected.log" 2>&1; then
  echo 'expected second receipt rejection to stop' >&2; exit 1
fi
[ "$(cat "$TOPOLOGY_RUNS/dispatched")" = 2 ]
[ "$before" = "$(sha256sum "$TOPOLOGY_LEDGER")" ]
[ ! -e "$TOPOLOGY_RUNS/inflight.edn" ]
[ -s "$TOPOLOGY_RUNS/jobs/test-1.receipt.edn" ]
[ -s "$TOPOLOGY_RUNS/jobs/test-2.receipt.edn" ]
reason="$(jq -r '.reason' "$TOPOLOGY_RUNS/last-rejected-receipt.json")"
grep -Fq "STOP: invalid receipt from test-2: $reason" "$scratch/rejected.log"
# The rejection counter is durable: restarting cannot grant a fresh free retry.
if MAX_ITER=2 bash "$scratch/loop.sh" > "$scratch/restart.log" 2>&1; then
  echo 'expected persisted rejection to stop on next rejected attempt' >&2; exit 1
fi
[ "$(cat "$TOPOLOGY_RUNS/dispatched")" = 3 ]
grep -Fq "STOP: invalid receipt from test-3: $reason" "$scratch/restart.log"
echo 'rejected-receipt tests: PASS (retry, fresh nonce, valid apply, repeated rejection, restart)'
