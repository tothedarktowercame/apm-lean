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
ROOT="${TOPOLOGY_ROOT:-/home/joe/code/apm-lean}"
# Ledger and run directory match the loop's, so a second campaign supervises
# its own ledger and writes its own logs instead of interleaving with this one.
LEDGER="${TOPOLOGY_LEDGER:-$HERE/worklist.edn}"
RUNS="${TOPOLOGY_RUNS:-$HERE/runs}"
LOG="$RUNS/build-loop.log"
SUPLOG="$RUNS/supervisor.log"
mkdir -p "$RUNS"
AGENCY="${AGENCY_BASE:-http://127.0.0.1:7070}"
SEND="${TOPOLOGY_SEND:-/home/joe/code/futon3c/scripts/agency_send.py}"
REPAIR_SEAT="${TOPOLOGY_REPAIR_SEAT:-}"
MAX_REPAIRS="${TOPOLOGY_MAX_REPAIRS:-3}"
REPAIR_TIMEOUT="${TOPOLOGY_REPAIR_TIMEOUT:-1800}"
ESCALATE_TO="${TOPOLOGY_ESCALATE_TO:-claude-7}"
MAX_ESCALATIONS="${TOPOLOGY_MAX_ESCALATIONS:-2}"
ESCALATION_TIMEOUT="${TOPOLOGY_ESCALATION_TIMEOUT:-3600}"
ESCALATION_POLL="${TOPOLOGY_ESCALATION_POLL:-60}"

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
    # PROVIDER QUOTA. No agent can repair "you've hit your usage limit" -- the
    # remedy is money, a different provider, or waiting for the weekly reset.
    # Retrying spends the repair budget on jobs that fail instantly and, because
    # every exhausted budget escalates to a Claude seat, burns the quota of a
    # DIFFERENT provider to report a problem nobody can fix. On 2026-09-09 the
    # Codex account hit 100% weekly with a reset five days out while the Claude
    # account sat at 95%, so three futile repairs plus an escalation was the
    # worst possible use of what was left. Stop and tell a human once.
    *"usage limit"*|*"quota"*|*"rate limit"*|*"purchase more credits"*) return 0 ;;
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
  local reason="$1" note out
  note="$(mktemp)"
  { echo "topology-supervisor: automated repair is exhausted after $MAX_REPAIRS attempts."
    echo "last stop: $reason"
    echo "This needs a human or a more capable agent. The loop is stopped."
    echo
    echo "You do NOT need to restart it. This supervisor waits up to"
    echo "${ESCALATION_TIMEOUT}s and restarts the loop itself as soon as the ledger"
    echo "validates and the worktree is clean. COMMIT your fix -- an uncommitted one"
    echo "leaves the tree dirty, which is one of the two things being waited on."
    echo; echo "== validator =="; bb "$HERE/worklist_check.bb" "$LEDGER" 2>&1 | tail -10
    echo; echo "== last 40 log lines =="; tail -40 "$LOG"; } > "$note"
  # A bell, not a whistle. A whistle blocks until the recipient ANSWERS, and
  # this supervisor never reads the answer -- it judges recovery by healthy().
  # On 2026-09-08 the escalation was dispatched at 07:24:48 and logged
  # "escalation failed" at 07:26:49: 121 seconds, which is the timeout below,
  # not a delivery failure. The request had arrived and was being worked on.
  # Any escalation worth making takes longer to answer than a delivery timeout
  # should ever wait, so ask for delivery and judge the repair by the world.
  out="$(timeout 120 python3 "$SEND" --from topology-supervisor --to "$ESCALATE_TO" \
           --kind bell --type request --mode work < "$note" 2>&1 | tail -1)"
  rm -f "$note"
  printf '%s\n' "$out" >> "$SUPLOG"
  case "$out" in
    *'"accepted":true'*) slog "escalation delivered to $ESCALATE_TO"; return 0 ;;
    *) slog "escalation NOT delivered to $ESCALATE_TO: $(printf '%s' "$out" | head -c 200)"
       return 1 ;;
  esac
}

repairs=0
escalations=0
while true; do
  slog "starting loop (repairs used $repairs/$MAX_REPAIRS)"
  env MAX_ITER="${MAX_ITER:-1000}" DIRTY_WAIT_SECONDS="${DIRTY_WAIT_SECONDS:-900}" \
      "$HERE/topology-build-loop.sh"
  rc=$?
  [ "$rc" = 0 ] && { slog "loop exited cleanly (rc=0); supervisor done"; exit 0; }

  reason="$(last_stop_reason)"
  slog "loop exited rc=$rc reason='$reason'"

  if not_repairable "$reason"; then
    # A refusal still deserves ONE report, or the loop simply goes quiet and
    # the operator finds out hours later. The exception is a deliberate signal:
    # someone who stopped the loop on purpose does not need to be told they did.
    case "$reason" in
      *"received signal"*)
        slog "deliberate stop; leaving stopped, not escalating" ;;
      *)
        slog "not auto-repairable by policy; escalating once and leaving stopped"
        escalate "$reason" ;;
    esac
    exit "$rc"
  fi

  if [ "$repairs" -ge "$MAX_REPAIRS" ]; then
    # Escalating used to exit here, so a correct repair still left the loop
    # dead: on 2026-09-08 the ledger rule was diagnosed, fixed and committed by
    # 07:33 and the loop was still down at 07:41, because the only thing that
    # restarts it had already gone. The escalation asks for a repair; nothing
    # was left to notice when the repair arrived.
    if [ "$escalations" -ge "$MAX_ESCALATIONS" ]; then
      slog "escalated $escalations time(s) and still stopping; leaving stopped for a human"
      exit "$rc"
    fi
    escalations=$((escalations+1))
    slog "repair budget exhausted; escalating to $ESCALATE_TO ($escalations/$MAX_ESCALATIONS)"
    escalate "$reason" || true
    slog "waiting up to ${ESCALATION_TIMEOUT}s for the escalated repair to land"
    waited=0
    while [ "$waited" -lt "$ESCALATION_TIMEOUT" ]; do
      sleep "$ESCALATION_POLL"; waited=$((waited+ESCALATION_POLL))
      if healthy; then slog "healthy after ${waited}s; restarting loop"; break; fi
    done
    if ! healthy; then
      slog "still unhealthy after ${waited}s; leaving stopped for a human"
      exit "$rc"
    fi
    # Repairs stay exhausted on purpose: a stop after a human has been called
    # in belongs to them too, so the next one re-escalates instead of quietly
    # spending another automated attempt.
    continue
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
