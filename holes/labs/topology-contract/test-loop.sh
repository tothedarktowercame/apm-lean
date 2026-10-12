#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
suite_runs="$(mktemp -d)"
export TOPOLOGY_RUNS="$suite_runs"
trap 'rm -rf "$suite_runs"' EXIT
bb "$HERE/worklist_check.bb" "$HERE/worklist.edn"
TOPOLOGY_ALLOW_DIRTY=1 TOPOLOGY_NO_NOTIFY=1 "$HERE/topology-build-loop.sh" --dry-run
TOPOLOGY_NO_NOTIFY=1 "$HERE/topology-build-loop.sh" --replay "$HERE/fixtures/t02A03-replay.edn"

bad="$(mktemp)"
trap 'rm -f "$bad"; rm -rf "$suite_runs"' EXIT
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

# Scope is a write permission, not a requirement to touch every permitted
# path. Program rows name Main, status, closure, and blueprint even when one
# milestone changes only a subset. The real completion commit must pass with
# an additional permitted path, while the same commit remains rejected when
# its changed path is outside scope.
scope_subset="$(mktemp)"
sed 's#:scope \["problems/t02A03/lean/Main.lean"\]#:scope ["problems/t02A03/lean/Main.lean" "problems/t02A03/status.json"]#' \
  "$HERE/fixtures/transition-ledger.edn" > "$scope_subset"
bb "$HERE/build_step.bb" apply-result "$scope_subset" edge "$HERE/fixtures/done-receipt.edn"
bb "$HERE/worklist_check.bb" "$scope_subset"
rm -f "$scope_subset"

scope_violation="$(mktemp)"
sed 's#problems/t02A03/lean/Main.lean#problems/t02A03/status.json#' \
  "$HERE/fixtures/transition-ledger.edn" > "$scope_violation"
if bb "$HERE/build_step.bb" apply-result "$scope_violation" edge \
    "$HERE/fixtures/done-receipt.edn" >/dev/null 2>&1; then
  echo "expected out-of-scope commit rejection" >&2
  exit 1
fi
rm -f "$scope_violation"

stopped="$(mktemp)"
cp "$HERE/fixtures/transition-ledger.edn" "$stopped"
bb "$HERE/build_step.bb" apply-result "$stopped" edge "$HERE/fixtures/stop-receipt.edn"
[ "$(bb "$HERE/build_step.bb" unreviewed "$stopped")" = edge ]
bb "$HERE/build_step.bb" apply-result "$stopped" edge "$HERE/fixtures/pass-receipt.edn"
bb "$HERE/worklist_check.bb" "$stopped"
rm -f "$stopped"

# A PASS on a STOP says the stop was honest, not that the row delivered
# (2026-10-12: 190 such rows read as :done, unblocked their dependents, and
# banked 10 lemmas that were never declared). The row becomes :stopped, its
# dependent stays blocked, and the lemma it was elected for stays backlog.
stopdep="$(mktemp)"
bb -e '(let [d (clojure.edn/read-string (slurp (first *command-line-args*)))
             e (first (:items d))
             lem {:id :lemma-l :kind :lemma :state :backlog :phase :lemma :scope [] :depends-on []
                  :consumer (:consumer e) :other-consumers [] :acceptance {:lemma "l"}
                  :lemma {:name "l" :reported-by []}}
             after (-> e (assoc :id :after :kind :final-adapter :state :blocked :depends-on [:edge])
                       (dissoc :implements-lemma))]
         (spit (second *command-line-args*)
               (pr-str (assoc d :items [(assoc e :implements-lemma :lemma-l) lem after]))))' \
  "$HERE/fixtures/transition-ledger.edn" "$stopdep"
bb "$HERE/worklist_check.bb" "$stopdep"
bb "$HERE/build_step.bb" apply-result "$stopdep" edge "$HERE/fixtures/stop-receipt.edn"
bb "$HERE/build_step.bb" apply-result "$stopdep" edge "$HERE/fixtures/pass-receipt.edn"
[ "$(bb -e '(let [d (clojure.edn/read-string (slurp (first *command-line-args*))) s (into {} (map (juxt :id :state) (:items d)))] (print (s :edge) (s :lemma-l) (s :after)))' "$stopdep")" = ":stopped :backlog :blocked" ]
bb "$HERE/worklist_check.bb" "$stopdep"
rm -f "$stopdep"

# The 2026-09-30 cycle: author stops, review fails the stop, author stops
# again. The second stop must park the row for the owner: not reviewable, not
# schedulable.
cycle="$(mktemp)"
cp "$HERE/fixtures/transition-ledger.edn" "$cycle"
bb "$HERE/build_step.bb" apply-result "$cycle" edge "$HERE/fixtures/stop-receipt.edn"
bb "$HERE/build_step.bb" apply-result "$cycle" edge "$HERE/fixtures/fail-receipt.edn"
[ "$(bb "$HERE/build_step.bb" next-open "$cycle")" = edge ]
bb "$HERE/build_step.bb" apply-result "$cycle" edge "$HERE/fixtures/stop-receipt.edn"
[ -z "$(bb "$HERE/build_step.bb" unreviewed "$cycle")" ]
[ "$(bb "$HERE/build_step.bb" next-open "$cycle")" != edge ]
bb "$HERE/build_step.bb" row "$cycle" edge | grep -q ':state :needs-owner'
bb "$HERE/worklist_check.bb" "$cycle"
rm -f "$cycle"

# A row whose review fails TOPOLOGY_MAX_ROW_FAILS times also goes to the owner.
failing="$(mktemp)"
cp "$HERE/fixtures/transition-ledger.edn" "$failing"
for _ in 1 2 3 4; do
  bb "$HERE/build_step.bb" row "$failing" edge | grep -q ':state :needs-owner' && { echo "parked too early" >&2; exit 1; }
  bb "$HERE/build_step.bb" apply-result "$failing" edge "$HERE/fixtures/done-receipt.edn"
  bb "$HERE/build_step.bb" apply-result "$failing" edge "$HERE/fixtures/fail-receipt.edn"
done
bb "$HERE/build_step.bb" row "$failing" edge | grep -q ':state :needs-owner'
rm -f "$failing"

export TOPOLOGY_PROBLEMS_ROOT="$HERE/fixtures/problems"
checkpoint="$(mktemp)"
cp "$HERE/fixtures/checkpoint-ledger.edn" "$checkpoint"
# Need-driven admission: a row naming no open frozen problem is refused, and
# so is one whose only problem is already closed.
# tfix04 is open but its statement is not in fixtures/problems/STATEMENTS.json:
# only registered problems are electable consumers.
for unneeded in ':consumer :circle-fundamental-class' ':consumer :tfix03' ':consumer :tfix04'; do
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

# A checkpoint may declare a new lemma and elect its implementation in the
# same receipt.  Its explicit id must survive name-based upsert, and a work row
# that synthesized a different id from the qualified theorem name must be
# linked back to the unique lemma named by its exact declaration.
checkpoint_lemma="$(mktemp)"
cp "$HERE/fixtures/checkpoint-ledger.edn" "$checkpoint_lemma"
bb "$HERE/build_step.bb" apply-result "$checkpoint_lemma" checkpoint \
  "$HERE/fixtures/replan-with-explicit-lemma-id.edn"
bb "$HERE/worklist_check.bb" "$checkpoint_lemma"
bb "$HERE/build_step.bb" row "$checkpoint_lemma" lemma-short-explicit-id \
  | grep -q ':kind :lemma'
bb "$HERE/build_step.bb" row "$checkpoint_lemma" qualified-lemma-work \
  | grep -q ':implements-lemma :lemma-short-explicit-id'
rm -f "$checkpoint_lemma"

# Long qualified theorem names may share the first 80 normalized characters.
# They must become distinct lemma nodes rather than making the second upsert
# look like an attempt to rename the first node.
checkpoint_collision="$(mktemp)"
cp "$HERE/fixtures/checkpoint-ledger.edn" "$checkpoint_collision"
bb "$HERE/build_step.bb" add-lemmas "$checkpoint_collision" \
  "$HERE/fixtures/colliding-lemma-names.edn"
bb "$HERE/worklist_check.bb" "$checkpoint_collision"
[ "$(bb "$HERE/build_step.bb" row "$checkpoint_collision" \
      lemma-constructiontargets-manifoldfundamentalclass-integralrelativechainscomparisonwit \
      | grep -c 'integralRelativeChainsComparisonWithTransport')" = 1 ]
[ "$(grep -c ':kind :lemma' "$checkpoint_collision")" = 2 ]
rm -f "$checkpoint_collision"

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

sed -n '/^apply_job_result()/,/^}/p' "$HERE/topology-build-loop.sh" \
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

bash "$HERE/test-rejected-receipt.sh"
echo "topology-loop tests: PASS"
