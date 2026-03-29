#!/usr/bin/env bash
# APM Canaries Pipeline — run all 490 problems with retrospectives.
#
# Structure:
#   - Problems processed sequentially from manifest
#   - Every 10 problems: retrospective debrief
#   - Evidence accumulated per-problem
#   - Resume-safe: skips problems with existing solution + lean files
#
# Usage:
#   ./run-pipeline.sh              # run all from beginning
#   ./run-pipeline.sh --start 50   # resume from problem 50
#   ./run-pipeline.sh --batch 3    # run only batch 3 (problems 21-30)

set -euo pipefail

PIPELINE_DIR="$(cd "$(dirname "$0")" && pwd)"
MANIFEST="$PIPELINE_DIR/manifest/tasks.tsv"
BATCH_SIZE=10
START_FROM=1
SINGLE_BATCH=""

# Parse args
while [[ $# -gt 0 ]]; do
  case $1 in
    --start) START_FROM="$2"; shift 2 ;;
    --batch) SINGLE_BATCH="$2"; shift 2 ;;
    *) echo "Unknown option: $1"; exit 1 ;;
  esac
done

# Generate manifest if missing
if [ ! -f "$MANIFEST" ]; then
  echo "Generating manifest..."
  bash "$PIPELINE_DIR/generate-manifest.sh"
fi

TOTAL=$(tail -n+2 "$MANIFEST" | wc -l)
echo "=== APM Pipeline: $TOTAL problems, batch size $BATCH_SIZE ==="
echo "=== Start from: $START_FROM ==="
echo ""

# Read manifest into arrays
mapfile -t LINES < <(tail -n+2 "$MANIFEST")

PROBLEM_NUM=0
BATCH_NUM=0
BATCH_COUNT=0

for line in "${LINES[@]}"; do
  PROBLEM_NUM=$((PROBLEM_NUM + 1))

  # Skip if before start
  if [ "$PROBLEM_NUM" -lt "$START_FROM" ]; then
    continue
  fi

  # Parse TSV
  IFS=$'\t' read -r ID SUBJECT YEAR SESSION NUMBER PATH <<< "$line"
  BATCH_NUM=$(( (PROBLEM_NUM - 1) / BATCH_SIZE + 1 ))

  # Single-batch mode
  if [ -n "$SINGLE_BATCH" ] && [ "$BATCH_NUM" -ne "$SINGLE_BATCH" ]; then
    continue
  fi

  # Run problem
  echo ""
  echo "[$PROBLEM_NUM/$TOTAL] Problem: $ID (batch $BATCH_NUM)"
  bash "$PIPELINE_DIR/run-problem.sh" "$ID" "$PATH" "$BATCH_NUM" || {
    echo "WARNING: $ID failed, continuing..."
  }

  BATCH_COUNT=$((BATCH_COUNT + 1))

  # Retrospective every BATCH_SIZE problems
  if [ "$BATCH_COUNT" -ge "$BATCH_SIZE" ]; then
    echo ""
    echo "=========================================="
    echo "  RETROSPECTIVE: Batch $BATCH_NUM"
    echo "=========================================="
    bash "$PIPELINE_DIR/run-retrospective.sh" "$BATCH_NUM" || {
      echo "WARNING: Retrospective $BATCH_NUM failed, continuing..."
    }
    BATCH_COUNT=0

    # Single-batch mode: stop after the batch
    if [ -n "$SINGLE_BATCH" ]; then
      echo "Single-batch mode: done with batch $SINGLE_BATCH"
      break
    fi
  fi
done

# Final retrospective if incomplete batch
if [ "$BATCH_COUNT" -gt 0 ] && [ -z "$SINGLE_BATCH" ]; then
  FINAL_BATCH=$(( (PROBLEM_NUM - 1) / BATCH_SIZE + 1 ))
  echo ""
  echo "=========================================="
  echo "  RETROSPECTIVE: Final batch $FINAL_BATCH"
  echo "=========================================="
  bash "$PIPELINE_DIR/run-retrospective.sh" "$FINAL_BATCH" || true
fi

# Summary
echo ""
echo "=== Pipeline complete ==="
echo "Problems attempted: $PROBLEM_NUM"
echo "Evidence: $(ls "$PIPELINE_DIR/evidence/"*.json 2>/dev/null | wc -l) files"
echo "Solutions: $(ls "$PIPELINE_DIR/solutions/"*.md 2>/dev/null | wc -l) files"
echo "Lean proofs: $(ls "$PIPELINE_DIR/lean-proofs/"*.lean 2>/dev/null | wc -l) files"
echo "Retrospectives: $(ls "$PIPELINE_DIR/retrospectives/"*.md 2>/dev/null | wc -l) files"

# Quick lean status breakdown
if ls "$PIPELINE_DIR/evidence/"*.json >/dev/null 2>&1; then
  echo ""
  echo "Lean status breakdown:"
  grep -h '"lean_status"' "$PIPELINE_DIR/evidence/"*.json 2>/dev/null | sort | uniq -c | sort -rn
fi
