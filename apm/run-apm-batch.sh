#!/bin/bash
# Run APM problems in batch with resume support.
#
# Usage:
#   ./run-apm-batch.sh --canary              # just the 4 canaries
#   ./run-apm-batch.sh --subject topology    # all topology problems
#   ./run-apm-batch.sh --subject algebra --n 10  # first 10 algebra
#   ./run-apm-batch.sh --all --n 20          # first 20 of everything
#   ./run-apm-batch.sh --resume              # continue from where we left off
#
# Resume: checks canary dir for existing cheatsheets and skips done problems.
# Cooldown: 5 seconds between problems (configurable via --cooldown).

set -euo pipefail

APM_DIR="$HOME/code/storage/apm"
CANARY_DIR="$HOME/code/storage/canary"
MANIFEST="$APM_DIR/manifest.edn"

# Defaults
SUBJECT=""
MAX_N=999999
COOLDOWN=5
CANARY_ONLY=false
RESUME=false

# Parse args
while [[ $# -gt 0 ]]; do
  case "$1" in
    --subject) SUBJECT="$2"; shift 2 ;;
    --n) MAX_N="$2"; shift 2 ;;
    --cooldown) COOLDOWN="$2"; shift 2 ;;
    --canary) CANARY_ONLY=true; shift ;;
    --resume) RESUME=true; shift ;;
    --all) shift ;;
    *) echo "Unknown arg: $1"; exit 1 ;;
  esac
done

# Build problem list
if [ "$CANARY_ONLY" = true ]; then
  PROBLEMS=("t01A01" "a96A03" "b03J02" "m96A04")
else
  # Extract IDs from manifest, optionally filter by subject
  ALL_IDS=$(grep -oP ':id "\K[^"]+' "$MANIFEST")

  if [ -n "$SUBJECT" ]; then
    case "$SUBJECT" in
      topology)  PREFIX="t" ;;
      analysis)  PREFIX="a" ;;
      algebra)   PREFIX="b" ;;
      applied|functional) PREFIX="m" ;;
      *) echo "Unknown subject: $SUBJECT"; exit 1 ;;
    esac
    ALL_IDS=$(echo "$ALL_IDS" | grep "^${PREFIX}")
  fi

  PROBLEMS=()
  while IFS= read -r id; do
    PROBLEMS+=("$id")
  done <<< "$ALL_IDS"
fi

# Apply --n limit
if [ ${#PROBLEMS[@]} -gt "$MAX_N" ]; then
  PROBLEMS=("${PROBLEMS[@]:0:$MAX_N}")
fi

# Resume: skip already-done problems
DONE=0
SKIPPED=0
FAILED=0
TOTAL=${#PROBLEMS[@]}

echo "═══════════════════════════════════════════════════"
echo "  APM Batch Run"
echo "  $(date -Iseconds)"
echo "  Problems: $TOTAL"
[ -n "$SUBJECT" ] && echo "  Subject: $SUBJECT"
echo "  Cooldown: ${COOLDOWN}s"
echo "═══════════════════════════════════════════════════"
echo ""

for id in "${PROBLEMS[@]}"; do
  # Resume check: skip if cheatsheet PDF already exists
  if [ "$RESUME" = true ] && [ -f "$CANARY_DIR/$id.pdf" ]; then
    SKIPPED=$((SKIPPED + 1))
    continue
  fi

  echo "[$((DONE + SKIPPED + FAILED + 1))/$TOTAL] $id"

  if "$APM_DIR/run-apm-problem.sh" "$id" 2>&1 | sed 's/^/  /'; then
    DONE=$((DONE + 1))
  else
    FAILED=$((FAILED + 1))
    echo "  *** FAILED: $id ***"
  fi

  # Cooldown (skip after last problem)
  if [ $((DONE + SKIPPED + FAILED)) -lt "$TOTAL" ]; then
    sleep "$COOLDOWN"
  fi
done

echo ""
echo "═══════════════════════════════════════════════════"
echo "  Batch complete"
echo "  Done: $DONE  Skipped: $SKIPPED  Failed: $FAILED  Total: $TOTAL"
echo "  $(date -Iseconds)"
echo "═══════════════════════════════════════════════════"
