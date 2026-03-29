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
LEAN_DIR_PROB="$LEAN_DIR/${PROBLEM_ID}"
LEAN_FILE="$LEAN_DIR_PROB/Main.lean"
if [ ! -s "$LEAN_FILE" ]; then
  rm -rf "$LEAN_DIR_PROB"
  mkdir -p "$LEAN_DIR_PROB"
  echo "[$(date -Iseconds)] Generating Lean proof file-by-file (${LEAN_TIMEOUT}s total budget)..."

  PROBLEM_TEXT="$(cat "$TEX_PATH")"
  SOLUTION_EXCERPT="$(head -100 "$SOLUTION_FILE" 2>/dev/null || echo 'none')"
  LEAN_BUDGET_START=$(date +%s)

  # Step 1: Imports + Statement
  STEP1_PROMPT=$(mktemp)
  cat > "$STEP1_PROMPT" <<STEP1_EOF
Write ONLY the Lean 4 imports and theorem statement for this problem. Use Mathlib. Do NOT write the proof body — just end with := by sorry

Problem (${PROBLEM_ID}):
${PROBLEM_TEXT}

Output ONLY Lean code, no markdown fences.
STEP1_EOF
  echo "[$(date -Iseconds)]   Step 1: imports + statement..."
  cat "$STEP1_PROMPT" | timeout 180 claude -p - --output-format text > "$LEAN_DIR_PROB/Statement.lean" 2>/dev/null || true
  rm -f "$STEP1_PROMPT"
  echo "[$(date -Iseconds)]   Step 1 done: $(wc -l < "$LEAN_DIR_PROB/Statement.lean") lines"

  # Step 2: Helper lemmas (if needed)
  STEP2_PROMPT=$(mktemp)
  cat > "$STEP2_PROMPT" <<STEP2_EOF
Given this Lean 4 theorem statement:
$(cat "$LEAN_DIR_PROB/Statement.lean")

And this informal proof:
${SOLUTION_EXCERPT}

Write any helper lemmas needed for the proof. Import Mathlib at the top. Use sorry where Mathlib lacks coverage. If no helpers are needed, just write a comment saying so.

Output ONLY Lean code, no markdown fences.
STEP2_EOF
  echo "[$(date -Iseconds)]   Step 2: helper lemmas..."
  cat "$STEP2_PROMPT" | timeout 300 claude -p - --output-format text > "$LEAN_DIR_PROB/Lemmas.lean" 2>/dev/null || true
  rm -f "$STEP2_PROMPT"
  echo "[$(date -Iseconds)]   Step 2 done: $(wc -l < "$LEAN_DIR_PROB/Lemmas.lean") lines"

  # Step 3: Main proof
  ELAPSED=$(( $(date +%s) - LEAN_BUDGET_START ))
  REMAINING=$(( LEAN_TIMEOUT - ELAPSED ))
  if [ "$REMAINING" -gt 30 ]; then
    STEP3_PROMPT=$(mktemp)
    cat > "$STEP3_PROMPT" <<STEP3_EOF
Complete the main Lean 4 proof. Here is the statement:
$(cat "$LEAN_DIR_PROB/Statement.lean")

Here are the helper lemmas:
$(cat "$LEAN_DIR_PROB/Lemmas.lean")

Informal proof for reference:
${SOLUTION_EXCERPT}

Write the COMPLETE proof, incorporating the helpers. Import Mathlib. Use sorry ONLY where Mathlib genuinely lacks coverage. Output ONLY Lean code.
STEP3_EOF
    echo "[$(date -Iseconds)]   Step 3: main proof (${REMAINING}s remaining)..."
    cat "$STEP3_PROMPT" | timeout "$REMAINING" claude -p - --output-format text > "$LEAN_DIR_PROB/Main.lean" 2>/dev/null || true
    rm -f "$STEP3_PROMPT"
    echo "[$(date -Iseconds)]   Step 3 done: $(wc -l < "$LEAN_DIR_PROB/Main.lean") lines"
  else
    echo "[$(date -Iseconds)]   Step 3: skipped (only ${REMAINING}s remaining)"
    echo "-- Budget exhausted before main proof" > "$LEAN_DIR_PROB/Main.lean"
  fi

  # Assess result
  LEAN_FILE="$LEAN_DIR_PROB/Main.lean"
  if [ ! -s "$LEAN_FILE" ]; then
    LEAN_STATUS="generation-failed"
    echo "[$(date -Iseconds)] Lean generation produced empty file"
  else
    echo "[$(date -Iseconds)] Lean files written: $(wc -l "$LEAN_DIR_PROB"/*.lean | tail -1)"
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
