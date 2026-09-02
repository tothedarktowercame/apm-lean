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
MAX_ITER="${MAX_ITER:-60}"
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
valid_seat() { [[ "$1" =~ ^(codex-[0-9]+|claude-[0-9]+)$ ]] && [[ ! "$1" =~ ^f[0-9]+ ]]; }
notify() {
  local reason="$1" note
  [ "$NOTIFIED" = 1 ] && return 0
  NOTIFIED=1
  if [ "${TOPOLOGY_NO_NOTIFY:-0}" = 1 ]; then log "notification suppressed: $reason"; return 0; fi
  note="$(mktemp)"
  { echo "topology-build-loop: $reason"; echo "ledger: $LEDGER";
    echo "counts: $(bb "$HERE/build_step.bb" counts "$LEDGER" 2>/dev/null || true)";
    echo "last log lines:"; tail -40 "$LOG"; } > "$note"
  python3 /home/joe/code/futon3c/scripts/agency_send.py --from topology-build-loop \
    --to "$OWNER" --kind bell --type assert < "$note" >> "$LOG" 2>&1 || log "notification failed"
  rm -f "$note"
}
die() { log "STOP: $*"; notify "$*"; exit 1; }
on_exit() { local rc=$?; [ "$rc" = 0 ] || { [ "$NOTIFIED" = 1 ] || notify "unexpected exit code $rc"; }; }
trap on_exit EXIT
validate() { bb "$HERE/worklist_check.bb" "$LEDGER" >> "$LOG" 2>&1 || die "ledger validation failed"; }
repository_safe() {
  [ "$(readlink -f "$ROOT/.lake/packages")" = "/home/joe/code/apm-lean/.lake/packages" ] || die "wrong package authority"
  if [ "${TOPOLOGY_ALLOW_DIRTY:-0}" != 1 ] && [ -n "$(git -C "$ROOT" status --porcelain)" ]; then
    die "canonical worktree is dirty"
  fi
}
dispatch_and_wait() {
  local seat="$1" prompt="$2" label="$3" response job state elapsed=0
  valid_seat "$seat" || die "invalid regular seat: $seat"
  curl -fsS "$AGENCY/api/alpha/agents/$seat" | jq -e '.ok == true' >/dev/null || die "seat is not registered: $seat"
  log "$label dispatch to $seat"
  response="$(python3 /home/joe/code/futon3c/scripts/agency_send.py --from topology-build-loop \
    --to "$seat" --kind bell --type request --mode work < "$prompt")" || die "$label dispatch failed"
  job="$(jq -r '."job-id" // .job_id // empty' <<<"$response")"
  [ -n "$job" ] || die "$label returned no job id: $response"
  log "$label job=$job"
  while :; do
    state="$(curl -fsS "$AGENCY/api/alpha/invoke/jobs/$job" | jq -r '.job.state // empty')" || die "$label status read failed"
    case "$state" in
      done)
        LAST_JOB="$job"
        mkdir -p "$HERE/runs/jobs"
        LAST_RESULT="$HERE/runs/jobs/$job.result.txt"
        curl -fsS "$AGENCY/api/alpha/invoke/jobs/$job" | jq -r '.job.result // ""' > "$LAST_RESULT"
        log "$label done job=$job result=$LAST_RESULT"
        return 0 ;;
      failed|error|cancelled) die "$label terminal state=$state job=$job" ;;
      queued|running|accepted|"") ;;
      *) die "$label unknown state=$state job=$job" ;;
    esac
    sleep "$POLL_SECONDS"; elapsed=$((elapsed+POLL_SECONDS))
    if [ $((elapsed % 60)) -eq 0 ]; then log "$label heartbeat job=$job elapsed=${elapsed}s"; fi
  done
}
apply_job_result() {
  local row="$1" receipt
  receipt="$HERE/runs/jobs/$LAST_JOB.receipt.edn"
  sed -n 's/^TOPOLOGY_RECEIPT_EDN //p' "$LAST_RESULT" | tail -1 > "$receipt"
  [ -s "$receipt" ] || die "job $LAST_JOB emitted no TOPOLOGY_RECEIPT_EDN"
  bb "$HERE/build_step.bb" apply-result "$LEDGER" "$row" "$receipt" >> "$LOG" 2>&1 || die "invalid receipt from $LAST_JOB"
  git -C "$ROOT" add "$LEDGER"
  git -C "$ROOT" commit -q -m "topology-loop: record $row transition" || die "could not commit $row ledger transition"
}

if [ "$MODE" = replay ]; then
  [ -n "$REPLAY" ] || die "--replay needs a file"
  bb "$HERE/build_step.bb" replay "$REPLAY" | tee -a "$LOG"
  notify "REPLAY PASS: $REPLAY"
  exit 0
fi

validate
repository_safe
next="$(bb "$HERE/build_step.bb" next-open "$LEDGER")"
unreviewed="$(bb "$HERE/build_step.bb" unreviewed "$LEDGER")"
if [ "$MODE" = dry-run ]; then
  log "DRY RUN next-open=$next unreviewed=[$unreviewed] counts=$(bb "$HERE/build_step.bb" counts "$LEDGER")"
  exit 0
fi

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
    dispatch_and_wait "$REVIEW_SEAT" "$prompt" "review($unreviewed)"; rm -f "$prompt"
    apply_job_result "${unreviewed%% *}"
  else
    next="$(bb "$HERE/build_step.bb" next-open "$LEDGER")"
    if [ "$next" = NONE ]; then notify "DONE or exhausted: no open or unreviewed rows"; exit 0; fi
    row="$(bb "$HERE/build_step.bb" row "$LEDGER" "$next")"
    phase="$(sed -n 's/.*:phase :\([^ ,}]*\).*/\1/p' <<<"$row")"
    seat="$AUTHOR_SEAT"; [ "$phase" = probe ] && seat="$PROBE_SEAT"
    [ "$phase" = strategy ] && seat="$STRATEGY_SEAT"
    prompt="$(mktemp)"
    { echo "ROW TO DO THIS INVOCATION: $next"; echo "$row"; echo; cat "$HERE/work-prompt.md"; } > "$prompt"
    dispatch_and_wait "$seat" "$prompt" "work($next)"; rm -f "$prompt"
    apply_job_result "$next"
  fi
  validate
  key="$(sha256sum "$LEDGER" | cut -d' ' -f1)"
  if [ "$key" = "$STALL_KEY" ]; then STALL_N=$((STALL_N+1)); else STALL_KEY="$key"; STALL_N=0; fi
  [ "$STALL_N" -lt 3 ] || die "ledger unchanged for three iterations"
  [ "$ONCE" = 1 ] && { notify "ONE ITERATION complete"; exit 0; }
done
die "MAX_ITER=$MAX_ITER exhausted"
