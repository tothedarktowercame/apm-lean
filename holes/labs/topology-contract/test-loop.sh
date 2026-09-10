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

export TOPOLOGY_PROBLEMS_ROOT="$HERE/fixtures/problems"
checkpoint="$(mktemp)"
cp "$HERE/fixtures/checkpoint-ledger.edn" "$checkpoint"
# Need-driven admission: a row naming no open frozen problem is refused, and
# so is one whose only problem is already closed.
for unneeded in ':consumer :circle-fundamental-class' ':consumer :tfix03'; do
  unneeded_replan="$(mktemp)"
  sed "s/:consumer :tfix01/$unneeded/" "$HERE/fixtures/replan-receipt.edn" > "$unneeded_replan"
  before="$(sha256sum "$checkpoint" | cut -d' ' -f1)"
  if bb "$HERE/build_step.bb" apply-result "$checkpoint" checkpoint "$unneeded_replan" \
      >/dev/null 2>&1; then
    echo "expected need-driven rejection for $unneeded" >&2
    exit 1
  fi
  [ "$(sha256sum "$checkpoint" | cut -d' ' -f1)" = "$before" ]
  rm -f "$unneeded_replan"
done
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
invalid_revise="$(mktemp)"
sed 's/:phase :probe/:phase :probe :depends-on [:missing-dependency]/' \
  "$HERE/fixtures/revise-receipt.edn" > "$invalid_revise"
revised_before="$(sha256sum "$revised" | cut -d' ' -f1)"
if bb "$HERE/build_step.bb" apply-result "$revised" edge "$invalid_revise" \
    >/dev/null 2>&1; then
  echo "expected unknown prerequisite dependency rejection" >&2
  exit 1
fi
[ "$(sha256sum "$revised" | cut -d' ' -f1)" = "$revised_before" ]
rm -f "$invalid_revise"
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
# A GO on a :strategy-checkpoint would force :phase :implementation, which the
# ledger forbids (2026-09-10, oriented-checkpoint52). write-ledger! validates
# before its move, so the receipt is refused and the ledger is left untouched.
checkpoint_go="$(mktemp)"
cp "$HERE/fixtures/checkpoint-ledger.edn" "$checkpoint_go"
checkpoint_go_before="$(sha256sum "$checkpoint_go" | cut -d' ' -f1)"
if out="$(bb "$HERE/build_step.bb" apply-result "$checkpoint_go" checkpoint "$HERE/fixtures/go-receipt.edn" 2>&1)"; then
  echo "expected GO-on-strategy-checkpoint rejection" >&2
  exit 1
fi
grep -q 'would invalidate the ledger' <<<"$out"
[ "$(sha256sum "$checkpoint_go" | cut -d' ' -f1)" = "$checkpoint_go_before" ]
[ ! -e "$checkpoint_go.tmp" ]
rm -f "$checkpoint_go"

echo "topology-loop tests: PASS"
