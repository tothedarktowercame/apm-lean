#!/usr/bin/bash
# Run one APM problem through the full pipeline:
#   1. Parse LaTeX → problem statement
#   2. Claude: informal proof + lesson (Observe/Propose/Execute/Validate)
#   3. Claude: Lean formalisation (15-minute budget)
#   4. Lean build with timeout
#   5. Record evidence
#
# Usage: run-problem.sh <problem-id> <tex-path> <batch-number>

set -euo pipefail
export PATH="/usr/bin:/usr/local/bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"

PROBLEM_ID="${1:?Usage: run-problem.sh <problem-id> <tex-path> <batch-number>}"
TEX_PATH="${2:?}"
BATCH="${3:?}"
PIPELINE_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$PIPELINE_DIR")"
SOLUTIONS_DIR="$PIPELINE_DIR/solutions"
LEAN_DIR="$PIPELINE_DIR/lean-proofs"
EVIDENCE_DIR="$PIPELINE_DIR/evidence"

LEAN_TIMEOUT=900  # 15 minutes in seconds
START_TIME=$(date +%s)

echo "[$(date -Iseconds)] === $PROBLEM_ID (batch $BATCH) ==="

# 1. Read problem
PROBLEM_TEXT=$(cat "$TEX_PATH")
echo "[$(date -Iseconds)] Problem loaded ($(wc -c < "$TEX_PATH") bytes)"

# 2. Informal proof + lesson via Claude CLI
SOLUTION_FILE="$SOLUTIONS_DIR/${PROBLEM_ID}.md"
if [ ! -f "$SOLUTION_FILE" ]; then
  echo "[$(date -Iseconds)] Generating informal proof + lesson..."
  PROMPT_FILE=$(mktemp)
  cat > "$PROMPT_FILE" <<PROMPT_EOF
You are a mathematics tutor working through UT Austin preliminary exam problems. Use the futonic proof discipline:

PHASE 1 — OBSERVE: What is this problem really asking? What tools do you need? Explain any required background (Fatou, Closed Graph Theorem, etc.) from scratch for a strong-undergrad reader.

PHASE 2 — PROPOSE: What is the key insight that unlocks the problem? State it clearly before giving the proof.

PHASE 3 — EXECUTE: Give a clean, complete informal proof.

PHASE 4 — VALIDATE: Where would a student get stuck? What dead ends teach something? What traps does the problem set?

Format as markdown with sections: ## Setup, ## Key Insight, ## Proof, ## Where You'd Get Stuck

Problem (${PROBLEM_ID}):
$(cat "$TEX_PATH")
PROMPT_EOF
  cat "$PROMPT_FILE" | claude -p - --output-format stream-json --verbose 2>/dev/null \
    | python3 "$PIPELINE_DIR/stream-extract.py" "$SOLUTION_FILE"
  rm -f "$PROMPT_FILE"
  echo "[$(date -Iseconds)] Solution written ($(wc -w < "$SOLUTION_FILE") words)"
else
  echo "[$(date -Iseconds)] Solution already exists, skipping"
fi

# 3. Lean formalisation via Claude CLI (15-minute budget)
LEAN_FILE="$LEAN_DIR/${PROBLEM_ID}.lean"
LEAN_STATUS="skipped"
if [ ! -s "$LEAN_FILE" ]; then
  rm -f "$LEAN_FILE"  # remove empty files from prior failed runs
  echo "[$(date -Iseconds)] Generating Lean proof (${LEAN_TIMEOUT}s budget)..."
  LEAN_PROMPT_FILE=$(mktemp)
  cat > "$LEAN_PROMPT_FILE" <<LEAN_PROMPT_EOF
Write a Lean 4 proof for this UT Austin prelim problem using Mathlib.

Structure the output as SEPARATE SECTIONS delimited by:
  -- §IMPORTS
  -- §STATEMENT
  -- §LEMMA1 (helper lemma if needed)
  -- §LEMMA2 (helper lemma if needed)
  -- §MAIN

Each section should compile independently (repeat any needed imports/opens).
Use sorry ONLY where Mathlib genuinely lacks coverage — mark each sorry
with a comment explaining what's missing.

Start with imports and the theorem statement. Then build up lemmas.
Put the main theorem last. This way, even partial output is useful.

Problem (${PROBLEM_ID}):
$(cat "$TEX_PATH")

Informal proof for reference:
$(head -100 "$SOLUTION_FILE" 2>/dev/null || echo 'none')

Output ONLY the Lean code, no markdown fences.
LEAN_PROMPT_EOF
  # Stream Lean generation — tokens written to file as they arrive.
  # timeout wraps the whole pipeline; partial output survives kill.
  timeout "${LEAN_TIMEOUT}" /usr/bin/bash -c \
    "cat '$LEAN_PROMPT_FILE' | claude -p - --output-format stream-json --verbose 2>/dev/null \
     | python3 '$PIPELINE_DIR/stream-extract.py' '$LEAN_FILE'"
  LEAN_EXIT=$?
  rm -f "$LEAN_PROMPT_FILE"
  if [ $LEAN_EXIT -eq 124 ]; then
    LEAN_STATUS="timed-out"
    echo "[$(date -Iseconds)] Lean generation timed out (partial file: $(wc -l < "$LEAN_FILE") lines)"
  elif [ ! -s "$LEAN_FILE" ]; then
    LEAN_STATUS="generation-failed"
    echo "[$(date -Iseconds)] Lean generation produced empty file"
  else
    echo "[$(date -Iseconds)] Lean file written ($(wc -l < "$LEAN_FILE") lines)"
    # 4. Try to build
    SORRY_IN_FILE=$(grep -c "sorry" "$LEAN_FILE" 2>/dev/null || echo 0)
    echo "[$(date -Iseconds)] Building Lean proof (${SORRY_IN_FILE} sorry in source)..."
    LEAN_BUILD_LOG="$EVIDENCE_DIR/${PROBLEM_ID}-lean-build.log"
    export PATH="$HOME/.elan/bin:$PATH"
    # Copy to project and build
    cp "$LEAN_FILE" "$PROJECT_DIR/ApmCanaries/Current.lean"
    cd "$PROJECT_DIR"
    timeout "${LEAN_TIMEOUT}" lake build ApmCanaries.Current \
      > "$LEAN_BUILD_LOG" 2>&1
    BUILD_EXIT=$?
    cd "$PIPELINE_DIR"
    if [ $BUILD_EXIT -eq 0 ]; then
      if grep -q "sorry" "$LEAN_FILE"; then
        LEAN_STATUS="partial"
        SORRY_COUNT=$(grep -c "sorry" "$LEAN_FILE")
        echo "[$(date -Iseconds)] Lean: partial ($SORRY_COUNT sorry)"
      else
        LEAN_STATUS="closed"
        echo "[$(date -Iseconds)] Lean: CLOSED (zero sorry)"
      fi
    elif [ $BUILD_EXIT -eq 124 ]; then
      LEAN_STATUS="build-timed-out"
      echo "[$(date -Iseconds)] Lean build timed out"
    else
      LEAN_STATUS="build-failed"
      echo "[$(date -Iseconds)] Lean build failed"
    fi
    rm -f "$PROJECT_DIR/ApmCanaries/Current.lean"
  fi
else
  echo "[$(date -Iseconds)] Lean file already exists, skipping"
  if grep -q "sorry" "$LEAN_FILE"; then
    LEAN_STATUS="partial"
  else
    LEAN_STATUS="closed"
  fi
fi

# 5. Record evidence
END_TIME=$(date +%s)
ELAPSED=$((END_TIME - START_TIME))

cat > "$EVIDENCE_DIR/${PROBLEM_ID}.json" <<EVIDENCE
{
  "problem_id": "${PROBLEM_ID}",
  "batch": ${BATCH},
  "timestamp": "$(date -Iseconds)",
  "elapsed_seconds": ${ELAPSED},
  "solution_exists": $([ -f "$SOLUTION_FILE" ] && echo true || echo false),
  "solution_words": $(wc -w < "$SOLUTION_FILE" 2>/dev/null || echo 0),
  "lean_status": "${LEAN_STATUS}",
  "lean_lines": $(wc -l < "$LEAN_FILE" 2>/dev/null || echo 0),
  "sorry_count": $(grep -c "sorry" "$LEAN_FILE" 2>/dev/null || echo 0)
}
EVIDENCE

echo "[$(date -Iseconds)] Done: ${PROBLEM_ID} — ${LEAN_STATUS} (${ELAPSED}s)"
