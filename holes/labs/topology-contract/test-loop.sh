#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bb "$HERE/worklist_check.bb" "$HERE/worklist.edn"
TOPOLOGY_ALLOW_DIRTY=1 TOPOLOGY_NO_NOTIFY=1 "$HERE/topology-build-loop.sh" --dry-run
TOPOLOGY_NO_NOTIFY=1 "$HERE/topology-build-loop.sh" --replay "$HERE/fixtures/t02A03-replay.edn"

bad="$(mktemp)"
trap 'rm -f "$bad"' EXIT
sed '0,/:depends-on \[\]/s//:depends-on [:edge]/' \
  "$HERE/fixtures/transition-ledger.edn" > "$bad"
if bb "$HERE/worklist_check.bb" "$bad" >/dev/null 2>&1; then
  echo "expected cyclic ledger rejection" >&2
  exit 1
fi

transition="$(mktemp)"
cp "$HERE/fixtures/transition-ledger.edn" "$transition"
bb "$HERE/build_step.bb" apply-result "$transition" edge "$HERE/fixtures/go-receipt.edn"
[ "$(bb "$HERE/build_step.bb" next-open "$transition")" = edge ]
bb "$HERE/build_step.bb" apply-result "$transition" edge "$HERE/fixtures/done-receipt.edn"
[ "$(bb "$HERE/build_step.bb" unreviewed "$transition")" = edge ]
bb "$HERE/build_step.bb" apply-result "$transition" edge "$HERE/fixtures/pass-receipt.edn"
bb "$HERE/worklist_check.bb" "$transition"
rm -f "$transition"

stopped="$(mktemp)"
cp "$HERE/fixtures/transition-ledger.edn" "$stopped"
bb "$HERE/build_step.bb" apply-result "$stopped" edge "$HERE/fixtures/stop-receipt.edn"
[ "$(bb "$HERE/build_step.bb" unreviewed "$stopped")" = edge ]
bb "$HERE/build_step.bb" apply-result "$stopped" edge "$HERE/fixtures/pass-receipt.edn"
bb "$HERE/worklist_check.bb" "$stopped"
rm -f "$stopped"

checkpoint="$(mktemp)"
cp "$HERE/fixtures/checkpoint-ledger.edn" "$checkpoint"
invalid_replan="$(mktemp)"
sed 's/:kind :final-adapter/:kind :reusable-theorem/' \
  "$HERE/fixtures/replan-receipt.edn" > "$invalid_replan"
checkpoint_before="$(sha256sum "$checkpoint" | cut -d' ' -f1)"
if bb "$HERE/build_step.bb" apply-result "$checkpoint" checkpoint "$invalid_replan" \
    >/dev/null 2>&1; then
  echo "expected invalid reusable-theorem replan rejection" >&2
  exit 1
fi
[ "$(sha256sum "$checkpoint" | cut -d' ' -f1)" = "$checkpoint_before" ]
rm -f "$invalid_replan"
bb "$HERE/build_step.bb" apply-result "$checkpoint" checkpoint "$HERE/fixtures/replan-receipt.edn"
[ "$(bb "$HERE/build_step.bb" unreviewed "$checkpoint")" = checkpoint ]
[ "$(bb "$HERE/build_step.bb" next-open "$checkpoint")" = NONE ]
bb "$HERE/build_step.bb" apply-result "$checkpoint" checkpoint "$HERE/fixtures/fail-receipt.edn"
[ "$(bb "$HERE/build_step.bb" next-open "$checkpoint")" = checkpoint ]
bb "$HERE/worklist_check.bb" "$checkpoint"
grep -q ':phase :strategy' "$checkpoint"
grep -q ':state :superseded' "$checkpoint"
bb "$HERE/build_step.bb" apply-result "$checkpoint" checkpoint "$HERE/fixtures/replan-receipt.edn"
bb "$HERE/build_step.bb" apply-result "$checkpoint" checkpoint "$HERE/fixtures/pass-receipt.edn"
[ "$(bb "$HERE/build_step.bb" next-open "$checkpoint")" = next-adapter ]
bb "$HERE/worklist_check.bb" "$checkpoint"
rm -f "$checkpoint"

checkpoint_stop="$(mktemp)"
cp "$HERE/fixtures/checkpoint-ledger.edn" "$checkpoint_stop"
bb "$HERE/build_step.bb" apply-result "$checkpoint_stop" checkpoint "$HERE/fixtures/stop-receipt.edn"
bb "$HERE/build_step.bb" apply-result "$checkpoint_stop" checkpoint "$HERE/fixtures/pass-receipt.edn"
grep -q ':state :needs-owner' "$checkpoint_stop"
bb "$HERE/worklist_check.bb" "$checkpoint_stop"
rm -f "$checkpoint_stop"

revised="$(mktemp)"
cp "$HERE/fixtures/transition-ledger.edn" "$revised"
bb "$HERE/build_step.bb" apply-result "$revised" edge "$HERE/fixtures/revise-receipt.edn"
[ "$(bb "$HERE/build_step.bb" next-open "$revised")" = prerequisite ]
bb "$HERE/worklist_check.bb" "$revised"
rm -f "$revised"

extracted="$(mktemp)"
"$HERE/extract-receipt.sh" "$HERE/fixtures/realistic-result.txt" test-nonce "$extracted"
grep -q '^\{:outcome :revise' "$extracted"
rm -f "$extracted"

grep -A12 '^apply_job_result()' "$HERE/topology-build-loop.sh" \
  | grep -q 'clear "$INFLIGHT"'

grep -q 'queued|delivering|running|accepted' "$HERE/topology-build-loop.sh"
echo "topology-loop tests: PASS"
