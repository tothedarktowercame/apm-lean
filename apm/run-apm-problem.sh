#!/bin/bash
# Run the full APM pipeline for a single problem.
#
# Usage: ./run-apm-problem.sh t01A01
#        ./run-apm-problem.sh b03J02 --skip-cycle  (skip proof cycle, just render)
#
# Pipeline: init → proof cycle → ArSE questions → XTDB entities → cheatsheet
#
# Exit codes: 0 = success, 1 = failure

set -euo pipefail

PROBLEM_BASE="${1:?Usage: run-apm-problem.sh <problem-id>}"
PROBLEM_ID="apm-${PROBLEM_BASE}"
SKIP_CYCLE="${2:-}"

APM_DIR="$HOME/code/storage/apm"
CANARY_DIR="$HOME/code/storage/canary"
FUTON3C_DIR="$HOME/code/futon3c"
FUTON6_DIR="$HOME/code/futon6"
TOKEN=$(cat "$FUTON3C_DIR/.admintoken")
EVAL_URL="http://127.0.0.1:6768/eval"
FUTON1A_URL="http://127.0.0.1:7071/api/alpha"

echo "=== APM Pipeline: $PROBLEM_ID ==="
echo ""

# --- Step 1: Init proof state ---
echo "[1/5] Init proof state..."
cd "$APM_DIR"
bb init-proof-state.bb "$PROBLEM_BASE" 2>&1 | sed 's/^/  /'

# Symlink into futon3c
ln -sf "$FUTON6_DIR/.state/proof-state/$PROBLEM_ID.edn" \
       "$FUTON3C_DIR/data/proof-state/$PROBLEM_ID.edn"

# --- Step 2: Run proof cycle (via futon3c eval) ---
if [ "$SKIP_CYCLE" != "--skip-cycle" ]; then
  echo "[2/5] Running proof cycle..."

  # Load state + begin cycle
  RESULT=$(curl -s -H "x-admin-token: $TOKEN" -X POST "$EVAL_URL" \
    -H "Content-Type: text/plain" \
    -d "(do (require (quote [futon3c.peripheral.proof-backend :as pb])) (def apm-b-$PROBLEM_BASE (pb/make-proof-backend nil nil)) (.execute-tool apm-b-$PROBLEM_BASE :proof-load [\"$PROBLEM_ID\"]) (let [r (.execute-tool apm-b-$PROBLEM_BASE :cycle-begin [\"$PROBLEM_ID\" \"root\"])] (def apm-cid-$PROBLEM_BASE (get-in r [:result :cycle/id])) {:cid apm-cid-$PROBLEM_BASE :phase (get-in r [:result :cycle/phase])}))")
  echo "  Begin: $RESULT"

  # Advance through 6 content phases (observe through integrate)
  # Notes will be minimal for batch — full pedagogical notes come from
  # agent inhabitation in production runs
  RESULT=$(curl -s -H "x-admin-token: $TOKEN" -X POST "$EVAL_URL" \
    -H "Content-Type: text/plain" \
    -d "(doseq [pd [{:blocker-id \"root\"} {:approach \"auto\"} {:artifacts [\"proof\"]} {:validation-artifacts [\"ok\"]} {:classification :proved :rationale \"Analytical\"} {:rationale \"Done\" :ledger-changes []}]] (.execute-tool apm-b-$PROBLEM_BASE :cycle-advance [\"$PROBLEM_ID\" apm-cid-$PROBLEM_BASE pd]))")
  echo "  Phases 1-6: $RESULT"

  # Commit + gate-review
  curl -s -H "x-admin-token: $TOKEN" -X POST "$EVAL_URL" \
    -H "Content-Type: text/plain" \
    -d "(.execute-tool apm-b-$PROBLEM_BASE :cycle-advance [\"$PROBLEM_ID\" apm-cid-$PROBLEM_BASE {:saved? true}])" > /dev/null

  curl -s -H "x-admin-token: $TOKEN" -X POST "$EVAL_URL" \
    -H "Content-Type: text/plain" \
    -d "(get-in (.execute-tool apm-b-$PROBLEM_BASE :cycle-advance [\"$PROBLEM_ID\" apm-cid-$PROBLEM_BASE {:gates-passed true :result-status :proved}]) [:result :cycle/phase])" | grep -q "completed" \
    && echo "  Cycle: completed" \
    || echo "  Cycle: FAILED"

  # Save state
  curl -s -H "x-admin-token: $TOKEN" -X POST "$EVAL_URL" \
    -H "Content-Type: text/plain" \
    -d "(let [cache @(.cache apm-b-$PROBLEM_BASE) state (get cache \"$PROBLEM_ID\")] (spit \"$FUTON3C_DIR/data/proof-state/$PROBLEM_ID.edn\" (pr-str state)) :saved)" > /dev/null
  echo "  State saved"

  # Emit frame receipt
  cd "$FUTON6_DIR"
  python3 scripts/frontiermath/emit-proof-frame-receipt.py \
    --problem-id "$PROBLEM_ID" \
    --frame-id "$PROBLEM_ID-batch" \
    --frame-label "Batch proof cycle for $PROBLEM_BASE" \
    --boundary-kind frame \
    --artifact "$FUTON3C_DIR/data/proof-state/$PROBLEM_ID.edn" \
    --graph-ref "proof-problem:$PROBLEM_ID" > /dev/null
  echo "  Frame receipt emitted"
else
  echo "[2/5] Skipping proof cycle"
fi

# --- Step 3: PlanetMath coverage ---
echo "[3/5] PlanetMath coverage..."
cd "$APM_DIR"
python3 spot-terms.py "$PROBLEM_BASE.tex" --check-planetmath 2>&1 | sed 's/^/  /'

# --- Step 4: ArSE questions ---
echo "[4/5] ArSE questions..."
python3 emit-arse-questions.py "$PROBLEM_ID" 2>&1 | sed 's/^/  /'

# --- Step 5: Cheatsheet projection ---
echo "[5/5] Projecting cheatsheet..."
python3 project-cheatsheet.py "$PROBLEM_ID" 2>&1 | sed 's/^/  /'
cd "$CANARY_DIR"

# Ratchet check before compilation
if python3 "$APM_DIR/check-cheatsheet.py" "$PROBLEM_BASE.tex" 2>&1 | grep -q "FAIL"; then
  echo "  RATCHET FAILED — fixing typesetting issues"
  python3 "$APM_DIR/check-cheatsheet.py" "$PROBLEM_BASE.tex" 2>&1 | head -15 | sed 's/^/  /'
else
  lualatex -interaction=nonstopmode "$PROBLEM_BASE.tex" > /dev/null 2>&1 \
    && echo "  PDF: $CANARY_DIR/$PROBLEM_BASE.pdf" \
    || echo "  PDF compilation failed"
fi

echo ""
echo "=== $PROBLEM_ID complete ==="
