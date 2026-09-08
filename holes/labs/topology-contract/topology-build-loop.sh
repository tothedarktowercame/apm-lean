#!/usr/bin/env bash
# Continuous topology campaign supervisor. Agency supplies visible named seats;
# this process waits synchronously for every invoke job before advancing.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
LEDGER="${TOPOLOGY_LEDGER:-$HERE/worklist.edn}"
LOG="$HERE/runs/build-loop.log"
AGENCY="${AGENCY_BASE:-http://localhost:7070}"
OWNER="${OWNER_SEAT:-codex-18}"
PROBE_SEAT="${PROBE_SEAT:-codex-12}"
AUTHOR_SEAT="${AUTHOR_SEAT:-codex-6}"
REVIEW_SEAT="${REVIEW_SEAT:-codex-20}"
STRATEGY_SEAT="${STRATEGY_SEAT:-codex-12}"
POLL_SECONDS="${POLL_SECONDS:-20}"
JOB_TIMEOUT="${JOB_TIMEOUT:-14400}"
STATUS_RETRIES="${STATUS_RETRIES:-5}"
MAX_ITER="${MAX_ITER:-60}"
INFLIGHT="$HERE/runs/inflight.edn"
HEARTBEAT="$HERE/runs/heartbeat.edn"
MODE=live
REPLAY=""
ONCE=0
NOTIFIED=0
mkdir -p "$HERE/runs"

while [ $# -gt 0 ]; do
  case "$1" in
    --dry-run) MODE=dry-run ;;
    --replay) MODE=replay; shift; REPLAY="$1" ;;
    --once) ONCE=1 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

log() { echo "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] $*" | tee -a "$LOG"; }
valid_seat() { [[ "$1" =~ ^(codex-[0-9]+|claude-[0-9]+)$ ]]; }
send_notice() {
  local reason="$1" note
  if [ "${TOPOLOGY_NO_NOTIFY:-0}" = 1 ]; then log "notification suppressed: $reason"; return 0; fi
  note="$(mktemp)"
  { echo "topology-build-loop: $reason"; echo "ledger: $LEDGER";
    echo "counts: $(bb "$HERE/build_step.bb" counts "$LEDGER" 2>/dev/null || true)";
    echo "last log lines:"; tail -40 "$LOG"; } > "$note"
  python3 /home/joe/code/futon3c/scripts/agency_send.py --from topology-build-loop \
    --to "$OWNER" --kind bell --type assert < "$note" >> "$LOG" 2>&1 || log "notification failed"
  rm -f "$note"
}
notify() { [ "$NOTIFIED" = 1 ] && return 0; NOTIFIED=1; send_notice "$1"; }
die() { log "STOP: $*"; notify "$*"; exit 1; }
on_signal() { die "received signal $1; in-flight job retained for restart recovery"; }
on_exit() { local rc=$?; [ "$rc" = 0 ] || { [ "$NOTIFIED" = 1 ] || notify "unexpected exit code $rc"; }; }
trap on_exit EXIT
trap 'on_signal INT' INT
trap 'on_signal TERM' TERM
trap 'on_signal HUP' HUP
validate() { bb "$HERE/worklist_check.bb" "$LEDGER" >> "$LOG" 2>&1 || die "ledger validation failed"; }
repository_safe() {
  [ "$(readlink -f "$ROOT/.lake/packages")" = "/home/joe/code/apm-lean/.lake/packages" ] || die "wrong package authority"
  [ "${TOPOLOGY_ALLOW_DIRTY:-0}" = 1 ] && return 0
  # A dirty tree means SOMEONE ELSE is mid-write, and this loop is not the only
  # committer on master: apm-land-certified.timer promotes certified solver
  # proofs here every 30 minutes, and a frame's own end-of-frame commits land
  # here too. Each holds the tree dirty for a second or two between `git
  # checkout <branch> -- <file>` and `git commit`.
  #
  # Dying on that is wrong twice over. It stops a long-running supervisor for a
  # condition that clears itself, and it stops it AFTER the landing has already
  # succeeded -- on 2026-09-07 the loop was killed at 19:02:52 by a landing that
  # committed cleanly seconds later, and nothing restarted it. A transient
  # sibling write is a reason to wait, not a reason to stop.
  #
  # Still fail closed: a tree left dirty by an abandoned edit is a real hazard
  # to a loop that commits, so give it a bounded wait and then die as before.
  local waited=0
  while [ -n "$(git -C "$ROOT" status --porcelain --untracked-files=no)" ]; do
    if [ "$waited" -ge "${DIRTY_WAIT_SECONDS:-60}" ]; then
      die "canonical tracked worktree is dirty (still dirty after ${waited}s)"
    fi
    [ "$waited" = 0 ] && log "canonical worktree dirty; waiting for the other writer"
    sleep 5
    waited=$((waited + 5))
  done
  [ "$waited" -gt 0 ] && log "canonical worktree clean after ${waited}s; continuing"
  return 0
}
job_json() {
  local job="$1" try=1 body
  while [ "$try" -le "$STATUS_RETRIES" ]; do
    if body="$(curl --connect-timeout 5 --max-time 20 -fsS "$AGENCY/api/alpha/invoke/jobs/$job")"; then
      printf '%s\n' "$body"; return 0
    fi
    log "job=$job status read attempt=$try/$STATUS_RETRIES failed"
    try=$((try+1)); sleep 5
  done
  return 1
}
wait_job() {
  local job="$1" label="$2" state elapsed=0 body
  while :; do
    printf '{:job %q :checked-at %q}\n' "$job" "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" > "$HEARTBEAT"
    body="$(job_json "$job")" || die "$label status reads exhausted; in-flight job retained"
    state="$(jq -r '.job.state // empty' <<<"$body")"
    case "$state" in
      done)
        LAST_JOB="$job"; mkdir -p "$HERE/runs/jobs"
        LAST_RESULT="$HERE/runs/jobs/$job.result.txt"
        jq -r '.job.result // ""' <<<"$body" > "$LAST_RESULT"
        log "$label done job=$job result=$LAST_RESULT"; return 0 ;;
      failed|error|cancelled) die "$label terminal state=$state job=$job" ;;
      queued|delivering|running|accepted|"") ;;
      *) die "$label unknown state=$state job=$job" ;;
    esac
    sleep "$POLL_SECONDS"; elapsed=$((elapsed+POLL_SECONDS))
    [ "$elapsed" -lt "$JOB_TIMEOUT" ] || die "$label timeout=${JOB_TIMEOUT}s job=$job; in-flight job retained"
    if [ $((elapsed % 60)) -eq 0 ]; then log "$label heartbeat job=$job elapsed=${elapsed}s"; fi
  done
}
dispatch_and_wait() {
  local seat="$1" prompt="$2" label="$3" row="$4" response job token augmented
  valid_seat "$seat" || die "invalid regular seat: $seat"
  token="$(printf '%s-%s-%s' "$row" "$(date +%s%N)" "$RANDOM" | sha256sum | cut -c1-24)"
  augmented="$(mktemp)"
  { cat "$prompt"; printf '\nReturn the result in THIS invoke job final response; do not bell, whistle, or open a separate reply thread. Your final machine receipt must be exactly one unindented line beginning:\nTOPOLOGY_RECEIPT_EDN %s {EDN map}\nDo not repeat that nonce elsewhere.\n' "$token"; } > "$augmented"
  log "$label dispatch to $seat receipt-token=$token"
  response="$(python3 /home/joe/code/futon3c/scripts/agency_send.py --from topology-build-loop \
    --to "$seat" --kind bell --type request --mode work < "$augmented")" || die "$label dispatch failed"
  rm -f "$augmented"
  job="$(jq -r '."job-id" // .job_id // empty' <<<"$response")"
  [ -n "$job" ] || die "$label returned no job id: $response"
  bb "$HERE/inflight.bb" write "$INFLIGHT" "$row" "$job" "$seat" "$token" "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" || die "could not persist in-flight job"
  log "$label job=$job"
  wait_job "$job" "$label"
}
apply_job_result() {
  local row="$1" token="$2" receipt transition
  receipt="$HERE/runs/jobs/$LAST_JOB.receipt.edn"
  if ! "$HERE/extract-receipt.sh" "$LAST_RESULT" "$token" "$receipt"; then
    # A completed job result is immutable. Retaining its in-flight pointer
    # makes every supervisor restart reclaim the same unusable result, so the
    # open row can never be dispatched again. Keep the result file as evidence,
    # clear only the pointer, and let the supervisor redispatch with a new nonce.
    bb "$HERE/inflight.bb" clear "$INFLIGHT" \
      || die "could not clear unusable in-flight job $LAST_JOB"
    die "job $LAST_JOB emitted no unique nonce-bound receipt"
  fi
  transition="$(bb "$HERE/build_step.bb" apply-result "$LEDGER" "$row" "$receipt" 2>&1)" || die "invalid receipt from $LAST_JOB: $transition"
  log "$transition"
  git -C "$ROOT" add "$LEDGER"
  git -C "$ROOT" commit -q -m "topology-loop: record $row transition $LAST_JOB" || die "could not commit $row ledger transition"
  bb "$HERE/inflight.bb" clear "$INFLIGHT" || die "could not clear committed in-flight job"
  send_notice "milestone applied: row=$row job=$LAST_JOB $transition"
}
resume_inflight() {
  [ -f "$INFLIGHT" ] || return 0
  local row job token seat
  row="$(bb "$HERE/inflight.bb" field "$INFLIGHT" row)"
  job="$(bb "$HERE/inflight.bb" field "$INFLIGHT" job)"
  token="$(bb "$HERE/inflight.bb" field "$INFLIGHT" token)"
  seat="$(bb "$HERE/inflight.bb" field "$INFLIGHT" seat)"
  [ -n "$row" ] && [ -n "$job" ] && [ -n "$token" ] || die "invalid $INFLIGHT"
  if [ "$(git -C "$ROOT" log -1 --pretty=%s)" = "topology-loop: record $row transition $job" ] &&
     git -C "$ROOT" diff --quiet -- "$LEDGER"; then
    log "reclaim found already-committed transition row=$row; clearing in-flight record"
    bb "$HERE/inflight.bb" clear "$INFLIGHT"
    return 0
  fi
  log "reclaim row=$row job=$job seat=$seat"
  wait_job "$job" "reclaim($row)"
  apply_job_result "$row" "$token"
}

if [ "$MODE" = replay ]; then
  [ -n "$REPLAY" ] || die "--replay needs a file"
  bb "$HERE/build_step.bb" replay "$REPLAY" | tee -a "$LOG"
  notify "REPLAY PASS: $REPLAY"
  exit 0
fi

validate
next="$(bb "$HERE/build_step.bb" next-open "$LEDGER")"
unreviewed="$(bb "$HERE/build_step.bb" unreviewed "$LEDGER")"
if [ "$MODE" = dry-run ]; then
  repository_safe
  log "DRY RUN next-open=$next unreviewed=[$unreviewed] counts=$(bb "$HERE/build_step.bb" counts "$LEDGER")"
  exit 0
fi
resume_inflight
repository_safe
send_notice "campaign started or resumed"

# --- seat resolution ------------------------------------------------------
# Joe, 2026-09-07: "knowing which entities are registered would not be hard.
# And then if one isn't registered, it wouldn't be used. And if not enough
# Codex agents were available, a new one could be registered. But stopping it
# and requiring a human intervention to get it unstuck for picking the
# incorrect pre-registered Codex agent is a bit strange to say the least."
#
# The loop used to check registration at DISPATCH time and die. That turned a
# stale seat name into a hard stop mid-campaign: on 2026-09-07 it stopped at
# 64 of 74 rows on "seat is not registered: codex-20" -- a seat that had worked
# on 2026-09-02 and was lost when the futon3c JVM restarted. The defaults in
# this file (codex-12, codex-20) had gone stale the same way, so any run
# started without seat env inherited the fault.
#
# Seats are now resolved ONCE, before any work: a configured seat that is
# registered is used as-is; one that is not is replaced from the registered
# pool; and if the pool cannot fill a distinct role, a fresh seat is registered
# via POST /api/alpha/agents/auto. Dying is reserved for the case where the
# Agency itself will not give us a seat -- a substrate failure, not a typo.
seat_registered() {
  curl -fsS --max-time 10 "$AGENCY/api/alpha/agents/$1" 2>/dev/null \
    | jq -e '.ok == true' >/dev/null 2>&1
}
registered_codex_seats() {
  curl -fsS --max-time 15 "$AGENCY/api/alpha/agents" 2>/dev/null \
    | jq -r '(.agents // .) | if type=="object" then [.[]] else . end
             | .[] | ."id"."id/value" // empty' 2>/dev/null \
    | grep -E '^codex-[0-9]+$' | sort -u
}
register_new_codex_seat() {
  curl -fsS --max-time 30 -X POST "$AGENCY/api/alpha/agents/auto" \
    -H 'Content-Type: application/json' -d '{"type":"codex"}' 2>/dev/null \
    | jq -r '."agent-id" // .id // empty' 2>/dev/null
}
# resolve_seat NAME CONFIGURED ALREADY_TAKEN...
resolve_seat() {
  local name="$1" want="$2"; shift 2
  local taken=" $* "
  if [ -n "$want" ] && seat_registered "$want" && [[ "$taken" != *" $want "* ]]; then
    printf '%s' "$want"; return 0
  fi
  local why="not registered"
  [[ "$taken" == *" $want "* ]] && why="already used by another role"
  local cand
  for cand in $(registered_codex_seats); do
    [[ "$taken" == *" $cand "* ]] && continue
    log "seat $name: $want is $why; using registered $cand instead" >&2
    printf '%s' "$cand"; return 0
  done
  local fresh; fresh="$(register_new_codex_seat)"
  if [ -n "$fresh" ] && [ "$fresh" != "null" ]; then
    log "seat $name: no free registered seat; registered $fresh" >&2
    printf '%s' "$fresh"; return 0
  fi
  die "seat $name: $want is $why and the Agency would not allocate a replacement"
}
OWNER="$(resolve_seat OWNER "$OWNER")"
REVIEW_SEAT="$(resolve_seat REVIEW "$REVIEW_SEAT" "$OWNER")"
AUTHOR_SEAT="$(resolve_seat AUTHOR "$AUTHOR_SEAT" "$REVIEW_SEAT")"
PROBE_SEAT="$(resolve_seat PROBE "$PROBE_SEAT" "$REVIEW_SEAT")"
STRATEGY_SEAT="$(resolve_seat STRATEGY "$STRATEGY_SEAT" "$REVIEW_SEAT")"
log "seats resolved: owner=$OWNER review=$REVIEW_SEAT author=$AUTHOR_SEAT probe=$PROBE_SEAT strategy=$STRATEGY_SEAT"

[ "$AUTHOR_SEAT" != "$REVIEW_SEAT" ] || die "author and reviewer seats are identical"
[ "$PROBE_SEAT" != "$REVIEW_SEAT" ] || die "probe and reviewer seats are identical"
[ "$STRATEGY_SEAT" != "$REVIEW_SEAT" ] || die "strategy and reviewer seats are identical"
i=0
STALL_KEY=""; STALL_N=0
while [ "$i" -lt "$MAX_ITER" ]; do
  i=$((i+1)); validate; repository_safe
  unreviewed="$(bb "$HERE/build_step.bb" unreviewed "$LEDGER")"
  if [ -n "$unreviewed" ]; then
    prompt="$(mktemp)"
    { echo "ROWS AWAITING REVIEW: $unreviewed -- review the first only."; cat "$HERE/review-prompt.md"; } > "$prompt"
    current="${unreviewed%% *}"
    dispatch_and_wait "$REVIEW_SEAT" "$prompt" "review($unreviewed)" "$current"; rm -f "$prompt"
    apply_job_result "$current" "$(bb "$HERE/inflight.bb" field "$INFLIGHT" token)"
  else
    next="$(bb "$HERE/build_step.bb" next-open "$LEDGER")"
    if [ "$next" = NONE ]; then
      counts="$(bb "$HERE/build_step.bb" counts "$LEDGER")"
      if [[ "$counts" == *":needs-owner"* || "$counts" == *":blocked"* ]]; then
        notify "PAUSED: no runnable rows; owner decision or strategy rewrite required"
      else
        notify "DONE: no open or unreviewed rows"
      fi
      exit 0
    fi
    row="$(bb "$HERE/build_step.bb" row "$LEDGER" "$next")"
    phase="$(sed -n 's/.*:phase :\([^ ,}]*\).*/\1/p' <<<"$row")"
    seat="$AUTHOR_SEAT"; [ "$phase" = probe ] && seat="$PROBE_SEAT"
    [ "$phase" = strategy ] && seat="$STRATEGY_SEAT"
    prompt="$(mktemp)"
    { echo "ROW TO DO THIS INVOCATION: $next"; echo "$row"; echo; cat "$HERE/work-prompt.md"; } > "$prompt"
    dispatch_and_wait "$seat" "$prompt" "work($next)" "$next"; rm -f "$prompt"
    apply_job_result "$next" "$(bb "$HERE/inflight.bb" field "$INFLIGHT" token)"
  fi
  validate
  key="$(sha256sum "$LEDGER" | cut -d' ' -f1)"
  if [ "$key" = "$STALL_KEY" ]; then STALL_N=$((STALL_N+1)); else STALL_KEY="$key"; STALL_N=0; fi
  [ "$STALL_N" -lt 3 ] || die "ledger unchanged for three iterations"
  [ "$ONCE" = 1 ] && { notify "ONE ITERATION complete"; exit 0; }
done
die "MAX_ITER=$MAX_ITER exhausted"
