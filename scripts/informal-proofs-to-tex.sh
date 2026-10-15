#!/usr/bin/env bash
# Convert APM Lean informal proofs (markdown) -> structural LaTeX, using the
# First Proof Sprint recipe (normalize-math-prose.py + pandoc + pandoc-mathify.lua).
# Sources under problems/<id>/informal-solution.md are NEVER mutated: all
# normalization happens on staged temporary copies.
#
# Usage: informal-proofs-to-tex.sh <id-list-file> [out-dir]
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CODE_ROOT="${APM_CODE_ROOT:-$(dirname "$REPO_ROOT")}"
FUTON6_ROOT="${FUTON6_ROOT:-$CODE_ROOT/futon6}"
STORAGE_ROOT="${APM_STORAGE_ROOT:-$CODE_ROOT/storage}"

NORMALIZER="$FUTON6_ROOT/scripts/normalize-math-prose.py"
FILTER="$FUTON6_ROOT/scripts/pandoc-mathify.lua"
SYNTAX="$REPO_ROOT/report/lean4.xml"

ID_LIST="${1:?usage: informal-proofs-to-tex.sh <id-list-file> [out-dir]}"
OUT_DIR="${2:-$STORAGE_ROOT/apm/first-proof-sprint/tex}"

for f in "$NORMALIZER" "$FILTER" "$SYNTAX" "$ID_LIST"; do
  [ -r "$f" ] || { echo "missing required input: $f" >&2; exit 1; }
done
command -v pandoc >/dev/null || { echo "pandoc not on PATH" >&2; exit 1; }

mkdir -p "$OUT_DIR"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

# Stage copies; refuse silently-missing sources rather than skipping them.
while read -r id; do
  [ -z "$id" ] && continue
  src="$REPO_ROOT/problems/$id/informal-solution.md"
  [ -r "$src" ] || { echo "no informal solution for $id" >&2; exit 1; }
  cp "$src" "$tmp_dir/apm-$id.md"
done < "$ID_LIST"

# Part of the corpus writes math as \(..\) / \[..\], which pandoc's gfm reader
# does not recognise -- it has no tex_math_single_backslash extension -- so the
# mathematics would arrive as prose. Swap to the delimiters that reader knows,
# before any pass that counts dollars.
python3 "$REPO_ROOT/scripts/latex-delims-to-dollars.py" --write "$tmp_dir"/*.md

# The prose is hard-wrapped, sometimes through the middle of an inline math
# span. pandoc will not read $...$ across a newline, so the span has to be made
# whole before anything else looks at it.
python3 "$REPO_ROOT/scripts/rejoin-split-math.py" --write "$tmp_dir"/*.md

# Snapshot after rejoining (so line numbers align) and before normalization,
# so the guard below can put back any line normalization breaks.
snap_dir="$tmp_dir/.before"
mkdir -p "$snap_dir"
cp "$tmp_dir"/*.md "$snap_dir"/

# normalize-math-prose is OFF by default for this corpus. It was tuned on
# futon6's own first-proof markdown, where underscores are pre-escaped and
# math is already delimited. Here its rules collide with each other and with
# the existing $..$ spans, and measured over all 501 files it makes the output
# strictly worse:
#
#                        with      without
#   escaped dollars       358          88
#   commands as text       79          36
#   unbalanced spans        4           0
#
# The job it would do -- lifting bare prose math -- is done downstream by
# pandoc-mathify.lua, which is Unicode-aware. Set APM_USE_NORMALIZER=1 to run
# it anyway and reproduce the comparison.
if [ "${APM_USE_NORMALIZER:-0}" = "1" ]; then
  python3 "$NORMALIZER" --write --allow-in-place "$tmp_dir"/*.md >/dev/null
fi

# pandoc only reads $...$ as math when the delimiters hug non-space characters.
python3 "$REPO_ROOT/scripts/tidy-math-delimiters.py" --write "$tmp_dir"/*.md

# Where normalization left a line's delimiters unparseable -- usually two rules
# wrapping overlapping text and sharing a delimiter -- restore the original
# line. pandoc-mathify.lua handles the bare Unicode perfectly well.
python3 "$REPO_ROOT/scripts/guard-math-wellformed.py" --before "$snap_dir" --after "$tmp_dir"

# The APM Lean markdown writes subscripts as bare "_" in prose; GFM would read
# each pair as emphasis and silently turn two subscripts into one italic run.
# Runs after the normalizer so real subscripts are already lifted into $..$.
python3 "$REPO_ROOT/scripts/protect-prose-subscripts.py" --write "$tmp_dir"/*.md

n=0
for src in "$tmp_dir"/*.md; do
  base="$(basename "$src" .md)"
  out="$OUT_DIR/$base.tex"
  # --syntax-definition: 90 of these solutions carry a ```lean fence, and
  # neither pandoc nor KSyntaxHighlighting ships a Lean grammar, so without it
  # every line of Lean in the prose comes back as one undifferentiated
  # \NormalTok. The same grammar highlights the Lean proofs proper; see
  # render-lean-proofs.py.
  pandoc "$src" \
    -f gfm-superscript-subscript \
    -t latex \
    --wrap=preserve \
    --syntax-definition "$SYNTAX" \
    --lua-filter "$FILTER" \
    -o "$out"
  # Same apostrophe-artifact cleanup as the canonical First Proof regen script.
  sed -i \
    -e "s/\\\\textquotesingle\\\\textquotesingle{}/''/g" \
    -e "s/\\\\textquotesingle\\\\textquotesingle/''/g" \
    "$out"
  n=$((n + 1))
done
# pandoc-mathify.lua picks math-span boundaries without tracking brace depth,
# so some spans end mid-group and cannot compile. Restore the invariant.
python3 "$REPO_ROOT/scripts/repair-math-spans.py" --write "$OUT_DIR"/apm-*.tex

# A run of Unicode superscripts would otherwise map to one ^{..} per character,
# i.e. a double superscript. Fold each run into a single script.
python3 "$REPO_ROOT/scripts/fold-unicode-scripts.py" --write "$OUT_DIR"/apm-*.tex

# \tag only works inside an equation environment, not inside \[ \].
python3 "$REPO_ROOT/scripts/promote-tagged-display.py" --write "$OUT_DIR"/apm-*.tex

# Link names the prose already writes in code spans to the Lean declarations
# that use them, so the Tufte margin beside the informal argument has something
# in it. Runs after the repair passes so it sees final \texttt spans.
python3 "$REPO_ROOT/scripts/annotate-lean-links.py" --write "$OUT_DIR"/apm-*.tex

# pdflatex, and any reader that parses the source as LaTeX, needs ASCII: write
# each remaining Unicode symbol as the command it means (math- or text-mode).
# Last of the passes over apm-*.tex, so the margin notes above are covered.
python3 "$REPO_ROOT/scripts/asciify-tex.py" --write "$OUT_DIR"/apm-*.tex

# The Lean proofs, highlighted, into a subdirectory so the repair passes above
# (which glob apm-*.tex) never see them: a Lean listing is not math prose.
python3 "$REPO_ROOT/scripts/render-lean-proofs.py" "$ID_LIST" "$OUT_DIR"

echo "Converted $n informal proofs -> $OUT_DIR/apm-*.tex"
