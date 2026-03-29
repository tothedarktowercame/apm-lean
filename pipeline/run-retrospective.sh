#!/usr/bin/env bash
# Generate a retrospective after a batch of 10 problems.
# Reads evidence files, summarises patterns, generates debrief.
#
# Usage: run-retrospective.sh <batch-number>

set -euo pipefail

BATCH="${1:?Usage: run-retrospective.sh <batch-number>}"
PIPELINE_DIR="$(cd "$(dirname "$0")" && pwd)"
EVIDENCE_DIR="$PIPELINE_DIR/evidence"
RETRO_DIR="$PIPELINE_DIR/retrospectives"
SOLUTIONS_DIR="$PIPELINE_DIR/solutions"

RETRO_FILE="$RETRO_DIR/batch-${BATCH}.md"
echo "[$(date -Iseconds)] Generating retrospective for batch $BATCH"

# Gather evidence for this batch
BATCH_EVIDENCE=$(find "$EVIDENCE_DIR" -name "*.json" -exec grep -l "\"batch\": *${BATCH}" {} \;)
PROBLEM_COUNT=$(echo "$BATCH_EVIDENCE" | grep -c . || echo 0)

if [ "$PROBLEM_COUNT" -eq 0 ]; then
  echo "No evidence found for batch $BATCH"
  exit 1
fi

# Summarise
CLOSED=$(echo "$BATCH_EVIDENCE" | xargs grep -l '"lean_status": "closed"' | wc -l || echo 0)
PARTIAL=$(echo "$BATCH_EVIDENCE" | xargs grep -l '"lean_status": "partial"' | wc -l || echo 0)
TIMED_OUT=$(echo "$BATCH_EVIDENCE" | xargs grep -l '"lean_status":.*timed' | wc -l || echo 0)
FAILED=$(echo "$BATCH_EVIDENCE" | xargs grep -l '"lean_status":.*failed' | wc -l || echo 0)

# Collect problem IDs for this batch
PROBLEM_IDS=$(echo "$BATCH_EVIDENCE" | xargs -I{} basename {} .json | sort)

# Build summary context for Claude
EVIDENCE_SUMMARY=""
for eid in $PROBLEM_IDS; do
  if [ -f "$EVIDENCE_DIR/${eid}.json" ]; then
    EVIDENCE_SUMMARY="${EVIDENCE_SUMMARY}
$(cat "$EVIDENCE_DIR/${eid}.json")"
  fi
done

# Collect solution excerpts (first 20 lines of each)
SOLUTION_EXCERPTS=""
for eid in $PROBLEM_IDS; do
  if [ -f "$SOLUTIONS_DIR/${eid}.md" ]; then
    SOLUTION_EXCERPTS="${SOLUTION_EXCERPTS}

=== ${eid} ===
$(head -30 "$SOLUTIONS_DIR/${eid}.md")"
  fi
done

# Generate retrospective via Claude
claude -p "You are conducting a Lakatos + Wittgenstein style seminar debrief for batch ${BATCH} of the APM prelim problem pipeline. ${PROBLEM_COUNT} problems were attempted.

Evidence summary:
${EVIDENCE_SUMMARY}

Solution excerpts:
${SOLUTION_EXCERPTS}

Previous retrospectives exist in: ${RETRO_DIR}/

Generate a structured retrospective addressing:

1. **Pattern recurrence.** Which proof techniques appeared most? Which dead ends repeated? Did the pipeline fail the same way twice (a discipline gap)?

2. **Question-pattern distribution.** Which QP types dominated? (QP-4 why-hard, QP-7 what-crux, QP-5 why-works, QP-1 what-connects, QP-8 confidence-inversion). Any new patterns emerging?

3. **Pedagogical quality check.** Sample one or two solutions: would the explanation help a strong undergrad who doesn't know the prerequisite tools? Or is it formulaic?

4. **Lean formalisation profile.** ${CLOSED} closed, ${PARTIAL} partial (sorry), ${TIMED_OUT} timed out, ${FAILED} failed. What do the sorry boundaries tell us about Mathlib coverage? Any patterns in what times out?

5. **Discipline adaptation.** What should change for the next batch? New QP pattern needed? Phase timing adjustment? Different Lean strategy?

6. **Cumulative observations.** What's the pipeline learning about itself across batches?

Format as markdown. Be specific — name problems, name patterns, give examples." --output-format text > "$RETRO_FILE" 2>/dev/null

echo "[$(date -Iseconds)] Retrospective written to $RETRO_FILE ($(wc -w < "$RETRO_FILE") words)"
