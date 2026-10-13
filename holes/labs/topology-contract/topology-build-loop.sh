#!/usr/bin/env bash
# Continuous topology campaign supervisor. Agency supplies visible named seats;
# this process waits synchronously for every invoke job before advancing.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
LEDGER="${TOPOLOGY_LEDGER:-$HERE/worklist.edn}"
# Every per-run artifact lives here. A second loop needs its own, or it
# shares this one's in-flight pointer and reclaims the other loop's job.
RUNS="${TOPOLOGY_RUNS:-$HERE/runs}"
LOG="$RUNS/build-loop.log"
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
INFLIGHT="$RUNS/inflight.edn"
HEARTBEAT="$RUNS/heartbeat.edn"
REJECTION="$RUNS/last-rejected-receipt.json"
MODE=live
REPLAY=""
ONCE=0
NOTIFIED=0
mkdir -p "$RUNS"

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
valid_seat() { [[ "$1" =~ ^(codex-[0-9]+|claude-[0-9]+|topo-[0-9]+)$ ]]; }
# Hoisted above the first die(): notice_target calls these, and validate()
# and repository_safe() can die long before the seat-resolution block runs.
# A function defined later than its caller is simply absent at that point.
seat_registered() {
  curl -fsS --max-time 10 "$AGENCY/api/alpha/agents/$1" 2>/dev/null \
    | jq -e '.ok == true' >/dev/null 2>&1
}
registered_codex_seats() {
  curl -fsS --max-time 15 "$AGENCY/api/alpha/agents" 2>/dev/null \
    | jq -r '(.agents // .) | if type=="object" then [.[]] else . end
             | .[] | ."id"."id/value" // empty' 2>/dev/null \
    | grep -E '^topo-[0-9]+$' | sort -u
}

# A notification must not be lost because its target name went stale. OWNER
# defaults to codex-18 and is only replaced by resolve_seat at startup LINE ~281
# -- but validate() and repository_safe() can die() well before that, so an
# early failure bells the unresolved default. On 2026-09-09 codex-18 was gone
# ("Agent not found") and six notifications 404'd, every one of them reporting a
# stop. The failures most worth reporting were precisely the ones whose report
# was silently dropped.
notice_target() {
  if seat_registered "$OWNER" 2>/dev/null; then printf '%s' "$OWNER"; return 0; fi
  local cand
  cand="$(registered_codex_seats 2>/dev/null | head -1)"
  if [ -n "$cand" ]; then
    # stderr: this function's value is captured with $(...), so a log line on
    # stdout would be captured INTO the seat name. Same trap as resolve_seat.
    log "notice target $OWNER is not registered; notifying $cand instead" >&2
    printf '%s' "$cand"; return 0
  fi
  # No registered seat at all: still emit to OWNER so the failure is visible in
  # the log as a failed send rather than silently skipped.
  printf '%s' "$OWNER"
}
send_notice() {
  local reason="$1" note target
  if [ "${TOPOLOGY_NO_NOTIFY:-0}" = 1 ]; then log "notification suppressed: $reason"; return 0; fi
  target="$(notice_target)"
  note="$(mktemp)"
  { echo "topology-build-loop: $reason"; echo "ledger: $LEDGER";
    echo "counts: $(bb "$HERE/build_step.bb" counts "$LEDGER" 2>/dev/null || true)";
    echo "last log lines:"; tail -40 "$LOG"; } > "$note"
  python3 /home/joe/code/futon3c/scripts/agency_send.py --from topology-build-loop \
    --to "$target" --kind bell --type assert < "$note" >> "$LOG" 2>&1 \
    || log "notification failed (target=$target)"
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
# Every registered statement must still match its approved fingerprint
# (problems/STATEMENTS.json, Joe 2026-09-28). A mismatch means someone changed
# an approved statement on master; no agent repairs that by itself, so the
# supervisor treats it as not repairable and a Claude seat or Joe decides.
statements_intact() {
  local out
  out="$(command python3 "$ROOT/scripts/statement-registry.py" check --rev HEAD 2>&1)" \
    || die "statement registry mismatch: $(tr '\n' ' ' <<<"$out" | cut -c1-400)"
}
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
# Codex reports an overflowing thread in two wordings (seen 2026-10-13).
is_context_overflow() {
  case "$1" in
    *"exceeds the context window"*|*"ran out of room in the model's context window"*) return 0 ;;
  esac
  return 1
}
# Clear the seat's session so its next job starts a fresh conversation.
reset_seat_session() {
  local seat="$1" body
  body="$(curl --connect-timeout 5 --max-time 20 -fsS -X POST \
    -H 'Content-Type: application/json' -d '{}' \
    "$AGENCY/api/alpha/agents/$seat/reset-session")" || return 1
  [ "$(jq -r '.ok // false' <<<"$body")" = true ] || return 1
  log "session reset seat=$seat old-session=$(jq -r '."old-session-id" // ."old_session_id" // "?"' <<<"$body")"
}
declare -A CONTEXT_RESETS=()
CURRENT_SEAT=""
wait_job() {
  local job="$1" label="$2" state elapsed=0 body term_reason fail_code
  while :; do
    printf '{:job %q :checked-at %q}\n' "$job" "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" > "$HEARTBEAT"
    if ! body="$(job_json "$job")"; then
      # A run of failed status reads says nothing about the immutable job's
      # state.  Keep polling the persisted job instead of stopping the whole
      # campaign or dispatching a duplicate job.  The ordinary job timeout
      # remains the bound if Agency never becomes readable again.
      log "$label status reads exhausted for job=$job; retaining job and continuing to poll"
      sleep "$POLL_SECONDS"; elapsed=$((elapsed+POLL_SECONDS))
      [ "$elapsed" -lt "$JOB_TIMEOUT" ] || die "$label timeout=${JOB_TIMEOUT}s job=$job; in-flight job retained"
      continue
    fi
    state="$(jq -r '.job.state // empty' <<<"$body")"
    case "$state" in
      done)
        LAST_JOB="$job"; mkdir -p "$RUNS/jobs"
        LAST_RESULT="$RUNS/jobs/$job.result.txt"
        jq -r '.job.result // ""' <<<"$body" > "$LAST_RESULT"
        log "$label done job=$job result=$LAST_RESULT"; return 0 ;;
      failed|error|cancelled)
        # Failures in the Agency's own bookkeeping, not the seat's work
        # (2026-09-29: futon1b queue waits of 120-145 s gave `store-busy` and
        # `activity-decision-failed`, and each cost a supervisor repair):
        # 1. The seat finished and wrote its receipt, and only the post-turn
        #    record failed. The receipt is in the last text event (the job's
        #    `result` is empty). Use it; the extractor still checks its nonce.
        # 2. The seat never executed anything. Whatever the code, this is a
        #    refusal before work began: resend after backoff, never repair.
        if [ "$state" = failed ]; then
          local last_text executed
          last_text="$(jq -r '[.job.events[]? | select(.type=="text") | .text] | last // ""' <<<"$body" 2>/dev/null)"
          executed="$(jq -r '.job.execution.executed // false' <<<"$body" 2>/dev/null)"
          # The seat's conversation thread has outgrown the model's context
          # window. Every later job on that thread fails the same way, so the
          # pre-execution resend below would retry forever (2026-10-13: the
          # three owners topo-1, topo-5 and topo-9 failed 105 jobs in a row,
          # backing off to 15 min each time). Give the seat a fresh thread and
          # resend at once. A second overflow on the fresh thread means the
          # prompt itself is too large; stop for diagnosis.
          if is_context_overflow "$last_text"; then
            bb "$HERE/inflight.bb" clear "$INFLIGHT" \
              || log "could not clear in-flight pointer for terminal job $job"
            if [ "${CONTEXT_RESETS[$CURRENT_SEAT]:-0}" -ge 1 ]; then
              die "$label job=$job context window exceeded again on $CURRENT_SEAT after a session reset"
            fi
            reset_seat_session "$CURRENT_SEAT" \
              || die "$label job=$job context window exceeded on $CURRENT_SEAT and the session reset failed"
            CONTEXT_RESETS[$CURRENT_SEAT]=1
            log "$label job=$job context window exceeded on $CURRENT_SEAT; session reset, resending"
            return 76
          fi
          if grep -q 'TOPOLOGY_RECEIPT_EDN' <<<"$last_text"; then
            LAST_JOB="$job"; mkdir -p "$RUNS/jobs"
            LAST_RESULT="$RUNS/jobs/$job.result.txt"
            printf '%s\n' "$last_text" > "$LAST_RESULT"
            log "$label job=$job failed after the seat finished ($(jq -r '.job."terminal-code" // "?"' <<<"$body")); using its receipt result=$LAST_RESULT"
            return 0
          fi
          if [ "$executed" != true ]; then
            bb "$HERE/inflight.bb" clear "$INFLIGHT" \
              || log "could not clear in-flight pointer for terminal job $job"
            log "$label job=$job failed before the seat executed anything ($(jq -r '.job."terminal-code" // "?"' <<<"$body")); resending"
            return 75
          fi
        fi
        # A terminal job is IMMUTABLE -- it will never become `done`. Retaining
        # its in-flight pointer makes every supervisor restart reclaim the same
        # dead job and die on it again: three identical reclaim stops inside 90
        # seconds on 2026-09-09, when codex-14's job failed because the Codex
        # account had hit 100% of its weekly quota. The row could never be
        # redispatched. This is the same reasoning the unusable-receipt path
        # already applies; the failed-job branch never got it.
        #
        # Clear the pointer so the row can be dispatched afresh. The job record
        # itself is untouched and remains the evidence.
        bb "$HERE/inflight.bb" clear "$INFLIGHT" \
          || log "could not clear in-flight pointer for terminal job $job"
        # Carry the agent's own last words into the stop reason. A bare
        # "terminal state=failed" sent a human to the job API to discover the
        # cause was a quota limit; the escalation packet should say so itself.
        term_reason="$(jq -r '[.job.events[]? | select(.type=="text") | .text] | last // ""' \
                        <<<"$body" 2>/dev/null | tr '\n' ' ' | cut -c1-200)"
        # The Agency's own failure code (e.g. futon1b-read-unavailable when the
        # evidence read is refused before the agent runs) goes into the stop
        # reason too: the agent's last text is empty in exactly those cases, and
        # the supervisor needs the code to tell a wait from a defect.
        fail_code="$(jq -r '[.job.events[]? | select(.type=="failed") | .code // empty] | last // ""' \
                      <<<"$body" 2>/dev/null)"
        [ -n "$term_reason" ] || term_reason="$(jq -r '[.job.events[]? | select(.type=="failed") | .message // empty] | last // ""' \
                      <<<"$body" 2>/dev/null | tr '\n' ' ' | cut -c1-200)"
        # Model capacity is a transient provider refusal before the seat has
        # executed any work. Returning 75 lets dispatch_and_wait issue a fresh
        # job and nonce after backoff. Dying here asks the supervisor to repair
        # a healthy repository; an already-running supervisor also cannot see
        # newly committed classifier changes until its own process restarts.
        if [[ "$term_reason" == *"Selected model is at capacity"* ]]; then
          log "$label job=$job refused by transient model capacity"
          return 75
        fi
        # The clock-decision store reports `store-busy` only when contention
        # prevents the turn from starting. Like model capacity above, this is
        # a transient pre-execution refusal: the immutable failed job remains
        # evidence, while dispatch_and_wait must issue a fresh job and nonce.
        if [ "$fail_code" = "store-busy" ]; then
          log "$label job=$job refused by transient clock-store contention"
          return 75
        fi
        # The activity decision can also fail after the agent has emitted text
        # but before Agency records a job result.  Such a job has no immutable
        # result for extract-receipt.sh to consume, so retry it through the
        # normal fresh-job/fresh-nonce path instead of stopping the loop or
        # reconstructing a receipt from event text.
        if [ "$fail_code" = "activity-decision-failed" ]; then
          log "$label job=$job lost its result to transient activity-decision failure"
          return 75
        fi
        # Codex can also lose the response stream after a turn has started.
        # Agency records that transport failure as the broad `invoke-error`
        # code, so classify only the explicit stream-disconnect message as
        # transient; other invoke errors still stop for diagnosis below.
        if [ "$fail_code" = "invoke-error" ] &&
           [[ "$term_reason" == *"stream disconnected before completion"* ]]; then
          log "$label job=$job lost its result to a transient response-stream disconnect"
          return 75
        fi
        die "$label terminal state=$state job=$job${fail_code:+ code=$fail_code}${term_reason:+ :: $term_reason}" ;;
      queued|delivering|running|accepted|"") ;;
      *) die "$label unknown state=$state job=$job" ;;
    esac
    sleep "$POLL_SECONDS"; elapsed=$((elapsed+POLL_SECONDS))
    [ "$elapsed" -lt "$JOB_TIMEOUT" ] || die "$label timeout=${JOB_TIMEOUT}s job=$job; in-flight job retained"
    if [ $((elapsed % 60)) -eq 0 ]; then log "$label heartbeat job=$job elapsed=${elapsed}s"; fi
  done
}
dispatch_and_wait() {
  local seat="$1" prompt="$2" label="$3" row="$4" response job token augmented wait_rc
  local capacity_waits=0 capacity_delay capacity_wait_max="${TOPOLOGY_CAPACITY_WAIT_MAX:-900}"
  valid_seat "$seat" || die "invalid regular seat: $seat"
  while :; do
    token="$(printf '%s-%s-%s' "$row" "$(date +%s%N)" "$RANDOM" | sha256sum | cut -c1-24)"
    augmented="$(mktemp)"
    { cat "$prompt"
      if [ -f "$REJECTION" ] && [ "$(jq -r '.row' "$REJECTION")" = "$row" ]; then
        printf '\nYour previous receipt for this row was rejected: %s\n' "$(jq -r '.reason | gsub("[\\r\\n]+"; " ")' "$REJECTION")"
      fi
      printf '\nThis is a work-mode job: execute at least one relevant verification command during THIS invocation, even when retrying previously completed work; reusing an earlier receipt without fresh tool execution is rejected.\nReturn the result in THIS invoke job final response; do not bell, whistle, or open a separate reply thread. Your final machine receipt must be exactly one unindented line beginning:\nTOPOLOGY_RECEIPT_EDN %s {EDN map}\nThe complete receipt line, including the prefix, MUST be at most 1800 bytes because longer final responses are truncated before the loop can read them. Keep every schema-required field, but make prose terse, omit successful command output, and abbreviate diagnostic history. Before responding, parse the exact map after the nonce with clojure.edn/read-string and verify the line byte count. Visual inspection is not an EDN syntax check. Do not repeat that nonce elsewhere.\n' "$token"; } > "$augmented"
    log "$label dispatch to $seat receipt-token=$token"
    response="$(python3 /home/joe/code/futon3c/scripts/agency_send.py --from topology-build-loop \
      --to "$seat" --kind bell --type request --mode work < "$augmented")" || die "$label dispatch failed"
    rm -f "$augmented"
    job="$(jq -r '."job-id" // .job_id // empty' <<<"$response")"
    [ -n "$job" ] || die "$label returned no job id: $response"
    bb "$HERE/inflight.bb" write "$INFLIGHT" "$row" "$job" "$seat" "$token" "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" || die "could not persist in-flight job"
    log "$label job=$job"
    CURRENT_SEAT="$seat"
    if wait_job "$job" "$label"; then CONTEXT_RESETS[$seat]=0; return 0; else wait_rc=$?; fi
    [ "$wait_rc" = 76 ] && continue
    [ "$wait_rc" = 75 ] || return "$wait_rc"
    capacity_waits=$((capacity_waits+1))
    capacity_delay=$((60 * (1 << (capacity_waits < 5 ? capacity_waits - 1 : 4))))
    [ "$capacity_delay" -gt "$capacity_wait_max" ] && capacity_delay="$capacity_wait_max"
    log "$label waiting ${capacity_delay}s after transient pre-execution refusal before fresh dispatch"
    sleep "$capacity_delay"
  done
}
apply_job_result() {
  local row="$1" token="$2" receipt transition extraction_error pending
  receipt="$RUNS/jobs/$LAST_JOB.receipt.edn"
  if ! extraction_error="$("$HERE/extract-receipt.sh" "$LAST_RESULT" "$token" "$receipt" 2>&1)"; then
    # A completed job result is immutable. Retaining its in-flight pointer
    # makes every supervisor restart reclaim the same unusable result, so the
    # open row can never be dispatched again. Keep the result file as evidence,
    # clear only the pointer, and let the supervisor redispatch with a new nonce.
    # Persist the extractor's exact complaint so the fresh dispatch tells the
    # agent why its previous receipt was unusable, just as the apply-result
    # rejection path below does for a schema-invalid receipt.
    pending="$(mktemp "$RUNS/.rejection.XXXXXX")" || die "could not create receipt rejection state"
    jq -n --arg row "$row" --arg reason "$extraction_error" '{row: $row, reason: $reason}' > "$pending" \
      && mv "$pending" "$REJECTION" || die "could not persist receipt rejection state"
    bb "$HERE/inflight.bb" clear "$INFLIGHT" \
      || die "could not clear unusable in-flight job $LAST_JOB"
    die "job $LAST_JOB emitted no unique nonce-bound receipt: $extraction_error"
  fi
  if ! transition="$(bb "$HERE/build_step.bb" apply-result "$LEDGER" "$row" "$receipt" 2>&1)"; then
    # The refused transition leaves the ledger unchanged. Preserve its receipt,
    # remember the row across restarts, and permit one fresh-nonce retry.
    local previous="" pending
    if [ -f "$REJECTION" ]; then
      previous="$(jq -er '.row' "$REJECTION")" || die "could not read receipt rejection state"
    fi
    pending="$(mktemp "$RUNS/.rejection.XXXXXX")" || die "could not create receipt rejection state"
    jq -n --arg row "$row" --arg reason "$transition" '{row: $row, reason: $reason}' > "$pending" \
      && mv "$pending" "$REJECTION" || die "could not persist receipt rejection state"
    bb "$HERE/inflight.bb" clear "$INFLIGHT" \
      || die "could not clear rejected in-flight job $LAST_JOB"
    log "REJECTED receipt from $LAST_JOB for $row: $transition"
    [ "$previous" != "$row" ] || die "invalid receipt from $LAST_JOB: $transition"
    return 1
  fi
  rm -f "$REJECTION" || die "could not clear receipt rejection state"
  log "$transition"
  # Both loops commit to the same repository. At 08:07:41 on 2026-10-10 they
  # applied receipts in the same second: topo2's commit held .git/index.lock,
  # topo1's unchecked `git add` failed on it, the staged diff below was empty,
  # and topo1 logged "nothing to commit" over its own uncommitted transition.
  # It then waited 15 min for "the other writer" (itself), stopped, and its
  # supervisor held the tree for hours while topo2 stopped on the same dirt.
  # So: one ledger commit at a time across loops (flock), a checked add with
  # retries for other committers' locks, and "already recorded" judged
  # against HEAD, not against whatever the index happens to hold.
  exec 8>"$ROOT/.git/topology-ledger-commit.lock"
  flock -w 300 8 || die "could not take the ledger commit lock"
  local add_try=1
  until git -C "$ROOT" add -- "$LEDGER"; do
    [ "$add_try" -lt 12 ] || die "could not stage $row ledger transition (index lock held?)"
    log "git add of ledger failed (attempt $add_try); retrying"
    add_try=$((add_try+1)); sleep 5
  done
  # Applying a receipt is IDEMPOTENT, and the reclaim path re-applies a
  # retained in-flight result on every restart. When someone else has already
  # applied and committed that same receipt -- a human, or one of the repair
  # agents this loop's own supervisor dispatches -- the re-apply is a no-op and
  # there is nothing to commit. `git commit` exits non-zero on that, and dying
  # there stopped the loop at 00:21:44 on 2026-09-09 immediately after an
  # escalated repair had correctly advanced the same row.
  #
  # An empty diff means the ledger already records this transition, which is
  # success. Check the LEDGER's staged diff specifically rather than swallowing
  # every commit failure -- a real one still dies.
  if git -C "$ROOT" diff --quiet HEAD -- "$LEDGER"; then
    log "ledger already records $row transition $LAST_JOB; nothing to commit"
  else
    # Path-scoped on purpose. A bare `git commit` takes whatever is staged,
    # and this repo has other committers -- the apm-land-certified timer, the
    # frames' own end-of-frame commits, and now a second topology loop. Naming
    # the ledger keeps this commit to the transition it claims to record.
    local commit_try=1
    until git -C "$ROOT" commit -q -m "topology-loop: record $row transition $LAST_JOB" -- "$LEDGER"; do
      [ "$commit_try" -lt 12 ] || die "could not commit $row ledger transition"
      log "git commit of ledger failed (attempt $commit_try); retrying"
      commit_try=$((commit_try+1)); sleep 5
    done
  fi
  exec 8>&-
  bb "$HERE/inflight.bb" clear "$INFLIGHT" || die "could not clear committed in-flight job"
  refresh_status "$row"
  send_notice "milestone applied: row=$row job=$LAST_JOB $transition"
}
# Keep problems/t*/status.json in line with the committed Lean, so a closure
# this loop makes is credited where open_problem_queue.clj reads it. Until
# 2026-09-28 nothing did this and 10 closed problems still recorded sorries.
# The refresh reads HEAD, not the shared working tree, and its commit is
# path-scoped to the files it changed. A failure is reported, not fatal: it is
# bookkeeping, and dying here would send a repair agent.
refresh_status() {
  local row="$1" changed
  if ! changed="$(command python3 "$ROOT/scripts/refresh-topology-status.py" 2>>"$LOG")"; then
    log "WARNING status.json refresh failed after $row"
    send_notice "status.json refresh failed after row=$row; see build-loop.log"
    return 0
  fi
  [ -n "$changed" ] || return 0
  # Same lock and checks as the ledger commit in apply_job_result: an add
  # that loses an index-lock race leaves status.json dirty, and a dirty tree
  # stops both loops.
  exec 8>"$ROOT/.git/topology-ledger-commit.lock"
  flock -w 300 8 || { log "WARNING could not take the commit lock for status.json after $row"; exec 8>&-; return 0; }
  local try=1
  # shellcheck disable=SC2086
  until git -C "$ROOT" add -- $changed; do
    [ "$try" -lt 12 ] || { log "WARNING could not stage status.json refresh after $row"; break; }
    try=$((try+1)); sleep 5
  done
  # shellcheck disable=SC2086
  if git -C "$ROOT" diff --quiet HEAD -- $changed; then
    exec 8>&-; return 0   # the other loop already committed the same counts
  fi
  try=1
  # shellcheck disable=SC2086
  until git -C "$ROOT" commit -q -m "topology-loop: refresh status.json after $row" -- $changed; do
    if [ "$try" -ge 12 ]; then log "WARNING could not commit status.json refresh after $row"; break; fi
    try=$((try+1)); sleep 5
  done
  [ "$try" -lt 12 ] && log "status.json refreshed after $row: $(echo $changed | wc -w) file(s)"
  exec 8>&-
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
  # Agency keeps job records in memory, so after it restarts (2026-09-07,
  # 09-27, and zone's rebuild before 10-10) the job answers 404 for good and
  # five failed status reads stop the loop on every supervisor restart. Each
  # time a human moved inflight.edn into orphaned/ by hand. Do that here: a
  # 404 is not a transient failure (a down Agency refuses the connection).
  # If this loop already fetched the result before it was stopped, apply that
  # copy; the receipt still has to carry this row's nonce.
  local code
  code="$(curl --connect-timeout 5 --max-time 20 -s -o /dev/null -w '%{http_code}' \
            "$AGENCY/api/alpha/invoke/jobs/$job")"
  if [ "$code" = 404 ]; then
    if [ -s "$RUNS/jobs/$job.result.txt" ]; then
      LAST_JOB="$job"; LAST_RESULT="$RUNS/jobs/$job.result.txt"
      log "reclaim($row) job=$job unknown to Agency; applying the result fetched before the stop"
      apply_job_result "$row" "$token"
      return
    fi
    mkdir -p "$RUNS/orphaned"
    local dest
    dest="$RUNS/orphaned/inflight-agency-lost-$(date -u '+%Y%m%dT%H%M%SZ').edn"
    mv "$INFLIGHT" "$dest"
    log "reclaim($row) job=$job unknown to Agency and no local result; moved in-flight record to $dest, row will be dispatched afresh"
    return 0
  fi
  CURRENT_SEAT="$seat"
  local reclaim_rc=0
  wait_job "$job" "reclaim($row)" || reclaim_rc=$?
  # 75/76: the retained job was refused (or its seat's thread overflowed and
  # was reset). wait_job has cleared the in-flight pointer, so the row is
  # dispatched afresh by the normal path; there is no result to apply.
  if [ "$reclaim_rc" = 75 ] || [ "$reclaim_rc" = 76 ]; then
    log "reclaim($row) job=$job not applied (rc=$reclaim_rc); row will be dispatched afresh"
    return 0
  fi
  [ "$reclaim_rc" = 0 ] || return "$reclaim_rc"
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
# Joe, 2026-09-27: topology seats are named topo-N, not codex-N. Standard
# codex-N names get picked up by other agents for unrelated work, which breaks
# a loop seat's focus; so the replacement pool is topo-N only, and a fresh seat
# is the next unused topo-N (the Codex runtime is the same; only the name differs).
# Joe, 2026-09-27: topo seats run on gpt-5.6-sol. Registered without a model,
# a Codex seat takes the CLI default (gpt-6-astra), which burns usage for no gain.
TOPOLOGY_SEAT_MODEL="${TOPOLOGY_SEAT_MODEL:-gpt-5.6-sol}"
register_new_codex_seat() {
  local n=1
  while seat_registered "topo-$n"; do n=$((n+1)); done
  curl -fsS --max-time 30 -X POST "$AGENCY/api/alpha/agents/restore" \
    -H 'Content-Type: application/json' \
    -d "{\"agent-id\":\"topo-$n\",\"type\":\"codex\",\"cwd\":\"/home/joe/code/\",\"memory-domain\":\"mathematics\",\"model\":\"$TOPOLOGY_SEAT_MODEL\"}" 2>/dev/null \
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
  i=$((i+1)); validate; repository_safe; statements_intact
  unreviewed="$(bb "$HERE/build_step.bb" unreviewed "$LEDGER")"
  if [ -n "$unreviewed" ]; then
    prompt="$(mktemp)"
    { echo "ROWS AWAITING REVIEW: $unreviewed -- review the first only."; cat "$HERE/review-prompt.md"; } > "$prompt"
    current="${unreviewed%% *}"
    dispatch_and_wait "$REVIEW_SEAT" "$prompt" "review($unreviewed)" "$current"; rm -f "$prompt"
    apply_job_result "$current" "$(bb "$HERE/inflight.bb" field "$INFLIGHT" token)" || continue
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
    apply_job_result "$next" "$(bb "$HERE/inflight.bb" field "$INFLIGHT" token)" || continue
  fi
  validate; statements_intact
  key="$(sha256sum "$LEDGER" | cut -d' ' -f1)"
  if [ "$key" = "$STALL_KEY" ]; then STALL_N=$((STALL_N+1)); else STALL_KEY="$key"; STALL_N=0; fi
  [ "$STALL_N" -lt 3 ] || die "ledger unchanged for three iterations"
  [ "$ONCE" = 1 ] && { notify "ONE ITERATION complete"; exit 0; }
done
die "MAX_ITER=$MAX_ITER exhausted"
