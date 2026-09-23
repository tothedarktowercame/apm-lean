#!/usr/bin/env bash
# Build the First Proof Sprint PDF from the converted proofs.
#
# Exists because the run needs three things that are easy to forget and whose
# absence is not obvious from the failure:
#
#   * TeX Live 2026 is at /usr/local/texlive and is NOT on PATH. Ubuntu's
#     partial texlive-latex-base shadows it at /usr/bin, so a bare `lualatex`
#     finds a toolchain missing most of what these proofs load.
#   * three .sty files from report/ have to sit beside the .tex. Without
#     math-proofread-style.sty the run dies at "Emergency stop" on line 1,
#     which reads like a document error and is not one.
#   * lualatex has to run twice, for the table of contents.
#
# Output goes to storage, never into the repo: run data is not source.
#
# Usage: build-sprint-pdf.sh [id-list] [tex-dir] [out-dir]
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CODE_ROOT="${APM_CODE_ROOT:-$(dirname "$REPO_ROOT")}"
STORAGE_ROOT="${APM_STORAGE_ROOT:-$CODE_ROOT/storage}"
TEXBIN="${TEXBIN:-/usr/local/texlive/2026/bin/x86_64-linux}"

IDS="${1:-$STORAGE_ROOT/apm/all-ids.txt}"
TEX_DIR="${2:-$STORAGE_ROOT/apm/full/tex}"
OUT_DIR="${3:-$STORAGE_ROOT/apm/full/pdf}"

[ -r "$IDS" ] || { echo "missing id list: $IDS" >&2; exit 1; }
[ -x "$TEXBIN/lualatex" ] || { echo "no lualatex at $TEXBIN" >&2; exit 1; }

mkdir -p "$OUT_DIR"
cp "$REPO_ROOT"/report/apm-unicode-math.sty \
   "$REPO_ROOT"/report/apm-pandoc-compat.sty \
   "$REPO_ROOT"/report/math-proofread-style.sty "$OUT_DIR/"

# --lean: the PDF does not carry the Lean proofs (Joe, 2026-09-23). They are a
# reading layer for the web edition, where each proof is its own page and the
# margin can gloss them; in the book they added 3,200 pages to a 1,700-page
# document that nobody reads linearly. The web build (publish-prelims.sh) keeps
# them. Pass --lean all here to put them back.
python3 "$REPO_ROOT/scripts/build-first-proof-sprint.py" \
  "$IDS" "$TEX_DIR" "$OUT_DIR/first-proof-sprint.tex" \
  --lean "${LEAN:-none}" --total "$(wc -l < "$IDS")"

cd "$OUT_DIR"
for pass in 1 2; do
  echo "== lualatex pass $pass =="
  PATH="$TEXBIN:$PATH" lualatex -interaction=nonstopmode \
    first-proof-sprint.tex > "pass$pass.log" 2>&1 || true
done

errors=$(grep -c '^! ' first-proof-sprint.log || true)
missing=$(grep -c 'Missing character' first-proof-sprint.log || true)
pages=$(PATH="$TEXBIN:$PATH" pdfinfo first-proof-sprint.pdf 2>/dev/null \
        | awk '/^Pages/{print $2}')
echo "   ${pages:-no} pages, $errors errors, $missing missing glyphs"
[ "$errors" = "0" ]
