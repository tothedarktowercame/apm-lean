#!/usr/bin/env bash
# Render the APM informal proofs to HTML and publish them under wip/prelims/.
#
# The chain, and why each step is there:
#
#   build-first-proof-sprint.py --latexml   an article, not a book: the other
#       LaTeXML pages under wip/ are articles, paper-site.css is written against
#       ltx-article, and the book class adds an ltx_page_navbar sidebar that
#       renders as a blank gutter down the left of every page.
#   latexmlc --splitat=section              one page per proof, cross-linked.
#       --timeout must be raised: the default 600s expires during XSLT on a
#       corpus this size, discarding the whole run at the last phase.
#   tuftify.py                              the Tufte measure, from futon5. Its
#       inline <style> is appended after every <link> so it wins the layout.
#   apply-wip-styling.py                    paper-site.css for the body face,
#       plus the two fixes a split render needs that a single-file paper does
#       not (page padding, and a navigation header that otherwise overstrikes).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CODE_ROOT="${APM_CODE_ROOT:-$(dirname "$REPO_ROOT")}"
STORAGE_ROOT="${APM_STORAGE_ROOT:-$CODE_ROOT/storage}"
TUFTIFY="${TUFTIFY:-$CODE_ROOT/futon5/holes/tech-notes/paper/html-build/wysiwyg/tuftify.py}"

IDS="${1:-$STORAGE_ROOT/apm/all-ids.txt}"
TEX_DIR="${2:-$STORAGE_ROOT/apm/full/tex}"
DOCROOT="${3:-/var/www/zone.hyperreal.enterprises/wip/prelims}"
WORK="${WORK:-$(mktemp -d)}"

for f in "$TUFTIFY" "$IDS"; do
  [ -r "$f" ] || { echo "missing required input: $f" >&2; exit 1; }
done
command -v latexmlc >/dev/null || { echo "latexmlc not on PATH" >&2; exit 1; }

echo "== source =="
python3 "$REPO_ROOT/scripts/build-first-proof-sprint.py" \
  "$IDS" "$TEX_DIR" "$WORK/prelims.tex" --latexml --total "$(wc -l < "$IDS")"

echo "== latexml =="
# Report the failure rather than dying mute: latexmlc gives up after 100 errors
# and exits non-zero, and under set -e that ended the run with nothing after
# "== latexml ==" in the log -- which looks identical to still being busy.
if ! ( cd "$WORK" && latexmlc --timeout=7000 --dest=index.html --format=html5 \
        --splitat=section prelims.tex > latexml.log 2>&1 ); then
  echo "   latexmlc failed:" >&2
  grep -E '^(Error|Fatal)' "$WORK/prelims.latexml.log" | head -20 >&2
  exit 1
fi
echo "   $(ls "$WORK"/*.html | wc -l) pages, $(grep -cE '^Error' "$WORK/latexml.log" || true) errors"

echo "== tufte =="
mkdir -p "$WORK/out"
cp "$WORK"/*.css "$WORK/out/" 2>/dev/null || true
n=0
for f in "$WORK"/*.html; do
  python3 "$TUFTIFY" "$f" -o "$WORK/out/$(basename "$f")" >/dev/null 2>&1 || cp "$f" "$WORK/out/"
  n=$((n + 1))
done
echo "   $n pages typeset"

python3 "$REPO_ROOT/scripts/apply-wip-styling.py" "$WORK/out"

echo "== publish =="
mkdir -p "$DOCROOT"
rm -f "$DOCROOT"/*.html "$DOCROOT"/*.css
cp "$WORK/out"/*.html "$WORK/out"/*.css "$DOCROOT"/
echo "   $(ls "$DOCROOT"/*.html | wc -l) pages -> $DOCROOT"
