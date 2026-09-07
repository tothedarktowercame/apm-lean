#!/usr/bin/env bash
# Supervise topology-build-loop.sh: when it stops, get it diagnosed, repaired
# and restarted by an agent instead of by a human.
#
# Joe, 2026-09-07: "the topology loop has stopped yet again ... that's the third
# such stoppage ... And it doesn't seem as though those stoppages are going to
# an agent who could almost certainly get us unblocked and get the fixes
# repaired and get the system moving again, much as we've been doing with the
# APM loop. So it's great that I'm seeing them as red boxes on voxterm. But it
# would be even better if we were getting the fixes deployed automatically."
#
# The loop already bells its OWNER on death -- but with --type assert, which
# TELLS an agent rather than ASKING one, and nothing waits for a fix or
# restarts. So every stop today ended at a human:
#
#   14:42  job emitted no unique nonce-bound receipt
#   18:11  ledger validation failed  (repair commit vs whole-row scope)
#   19:02  canonical tracked worktree is dirty
#   19:15  seat is not registered: codex-20
#   19:27  ledger validation failed  (REVISE re-inserted an existing row)
#
# Each was a small, diagnosable defect. Each cost a human round trip.
#
# This wrapper runs the loop, and on a non-zero exit dispatches a REPAIR
# request carrying the stop reason and the evidence, waits for it, revalidates,
# and restarts. It is deliberately conservative: see REFUSALS below.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT=/home/joe/code/apm-lean
LEDGER="$HERE/worklist.edn"
LOG="$HERE/runs/build-loop.log"
SUPLOG="$HERE/runs/supervisor.log"
AGENCY="${AGENCY_BASE:-http://127.0.0.1:7070}"
SEND=/home/joe/code/futon3c/scripts/agency_send.py
REPAIR_SEAT="${TOPOLOGY_REPAIR_SEAT:-}"
MAX_REPAIRS="${TOPOLOGY_MAX_REPAIRS:-3}"
REPAIR_TIMEOUT="${TOPOLOGY_REPAIR_TIMEOUT:-1800}"
ESCALATE_TO="${TOPOLOGY_ESCALATE_TO:-claude-7}"

slog() { echo "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] supervisor: $*" | tee -a "$SUPLOG"; }

# REFUSALS. Some stops must NOT be auto-repaired:
#   - a deliberate signal (an operator stopping the loop should stay stopped;
#     auto-restarting fights the person holding the keyboard)
#   - anything naming the package authority, which is a substrate guarantee and
#     not a defect an agent should paper over
not_repairable() {
  case "$1" in
    *"received signal"*) return 0 ;;
    *"wrong package authority"*) return 0 ;;
    # A dirty tree is another writer's UNCOMMITTED work. The loop already waits
    # DIRTY_WAIT_SECONDS for it, so reaching a stop means the tree stayed dirty
    # for the whole cap -- and the only thing a repair agent could do to "fix"
    # it is commit or discard work belonging to someone else. On 2026-09-07 the
    # tree was held for 215s by another agent mid-edit and cleared on its own;
    # an agent that had committed those files would have committed a
    # half-written test file as if it were finished. Escalate to a human.
    *"worktree is dirty"*) return 0 ;;
  *) return 1 ;;
  esac
}

last_stop_reason() {
  grep "STOP:" "$LOG" 2>/dev/null | tail -1 | sed 's/.*STOP: //'
}

pick_repair_seat() {
  [ -n "$REPAIR_SEAT" ] && { printf '%s' "$REPAIR_SEAT"; return 0; }
  curl -fsS --max-time 15 "$AGENCY/api/alpha/agents" 2>/dev/null \
    | jq -r '(.agents // .) | if type=="object" then [.[]] else . end
             | .[] | ."id"."id/value" // empty' 2>/dev/null \
    | grep -E '^codex-[0-9]+$' | sort -u | head -1
}

dispatch_repair() {
  local reason="$1" seat packet job
  seat="$(pick_repair_seat)"
  [ -n "$seat" ] || { slog "no repair seat available"; return 1; }
  packet="$(mktemp)"
  {
    echo "REPAIR REQUEST -- the topology build loop has stopped and needs you to fix it."
    echo
    echo "STOP REASON: $reason"
    echo
    echo "This supervisor restarts the loop as soon as the ledger validates and the"
    echo "worktree is clean, so a correct fix is all that is needed to resume. You are"
    echo "not being asked to advise; you are being asked to repair."
    echo
    echo "== validator =="
    bb "$HERE/worklist_check.bb" "$LEDGER" 2>&1 | tail -20
    echo
    echo "== ledger counts =="
    bb "$HERE/build_step.bb" counts "$LEDGER" 2>&1 | tail -3
    echo
    echo "== last 60 log lines =="
    tail -60 "$LOG"
    echo
    echo "== worktree =="
    git -C "$ROOT" status --porcelain --untracked-files=no | head -20
    echo
    cat <<'GUIDE'
HOW TO REPAIR

Diagnose from the evidence above, not from a guess. Read the validator's exact
complaint and the code that raises it -- worklist_check.bb for ledger rules,
build_step.bb for how receipts are applied, topology-build-loop.sh for the
supervisor's own preconditions.

Known failure families, all seen 2026-09-07, each of which took one small fix:

  "commit paths differ from exact scope"  a row completed via REPAIR spans more
      than one commit; evidence carries :commits and the check unions them.
  "duplicate item ids"  a receipt proposed a row whose id already exists.
      :replan refuses that; :revise used to insert anyway.
  "seat is not registered"  a seat name went stale across a JVM restart; seats
      are resolved against the live registry before any work.
  "canonical tracked worktree is dirty"  another writer holds the tree. That is
      a WAIT, not a defect -- DIRTY_WAIT_SECONDS controls it.

RULES

  - Repair the CAUSE. Do not edit worklist.edn to make a symptom disappear when
    the defect is in the code that writes it; a ledger edited to satisfy a
    checker is worse than a stopped loop.
  - If you must repair ledger data, use its own writer (build_step.bb's
    pprint), never text surgery. An id can appear in :depends-on as well as in
    :id, so a textual match can delete a row that merely NAMES the one you want.
  - Leave the tree clean and COMMIT your fix, with a message saying what stopped
    the loop and why the change is right. An uncommitted fix stops it again on
    the dirty-worktree gate.
  - Run `bb worklist_check.bb worklist.edn` before you finish. If it does not
    print "N items OK", you are not done.
  - Change the smallest thing that fixes the cause. Do not restart the loop
    yourself; this supervisor does that.
  - If you conclude it is NOT safely repairable, say so plainly and stop. An
    honest refusal is wanted; a guess that corrupts the ledger is not.

Report what stopped it, what you changed, and the validator's final line.
GUIDE
  } > "$packet"
  slog "dispatching repair to $seat: $reason"
  job="$(timeout 120 python3 "$SEND" --from topology-supervisor --to "$seat" \
          --kind bell --type request --mode work < "$packet" 2>&1 | tail -1)"
  rm -f "$packet"
  slog "repair dispatched: $(echo "$job" | head -c 200)"
  return 0
}

healthy() {
  bb "$HERE/worklist_check.bb" "$LEDGER" >/dev/null 2>&1 || return 1
  [ -z "$(git -C "$ROOT" status --porcelain --untracked-files=no)" ] || return 1
  return 0
}

escalate() {
  local reason="$1" note
  note="$(mktemp)"
  { echo "topology-supervisor: GIVING UP after $MAX_REPAIRS repair attempts."
    echo "last stop: $reason"
    echo "This needs a human or a more capable agent; automated repair did not"
    echo "restore the loop. The loop is NOT running."
    echo; echo "== validator =="; bb "$HERE/worklist_check.bb" "$LEDGER" 2>&1 | tail -10
    echo; echo "== last 40 log lines =="; tail -40 "$LOG"; } > "$note"
  timeout 120 python3 "$SEND" --from topology-supervisor --to "$ESCALATE_TO" \
    --kind whistle --type request < "$note" >> "$SUPLOG" 2>&1 || slog "escalation failed"
  rm -f "$note"
}

repairs=0
while true; do
  slog "starting loop (repairs used $repairs/$MAX_REPAIRS)"
  env MAX_ITER="${MAX_ITER:-1000}" DIRTY_WAIT_SECONDS="${DIRTY_WAIT_SECONDS:-900}" \
      "$HERE/topology-build-loop.sh"
  rc=$?
  [ "$rc" = 0 ] && { slog "loop exited cleanly (rc=0); supervisor done"; exit 0; }

  reason="$(last_stop_reason)"
  slog "loop exited rc=$rc reason='$reason'"

  if not_repairable "$reason"; then
    slog "not auto-repairable by policy; leaving stopped"
    exit "$rc"
  fi

  if [ "$repairs" -ge "$MAX_REPAIRS" ]; then
    slog "repair budget exhausted; escalating to $ESCALATE_TO"
    escalate "$reason"
    exit "$rc"
  fi
  repairs=$((repairs+1))

  dispatch_repair "$reason" || { slog "dispatch failed; escalating"; escalate "$reason"; exit "$rc"; }

  # Wait for the repair to take effect, judged by the world rather than by the
  # agent's say-so: the ledger validates and the tree is clean.
  slog "waiting up to ${REPAIR_TIMEOUT}s for the repair to land"
  waited=0
  while [ "$waited" -lt "$REPAIR_TIMEOUT" ]; do
    sleep 20; waited=$((waited+20))
    if healthy; then slog "healthy after ${waited}s; restarting loop"; break; fi
  done
  if ! healthy; then
    slog "still unhealthy after ${waited}s; escalating to $ESCALATE_TO"
    escalate "$reason"
    exit "$rc"
  fi
done
