"""Apply a prose rewrite to everything in a .tex file except the code listings.

The passes that repair generated LaTeX -- math-span balance, Unicode script
folding, display promotion -- are all about mathematics written as prose. A
code listing is neither: its braces belong to pandoc's token macros, and its
Unicode is Lean's own (`x⁻¹`, `aₐ`, `∫₀` are identifiers and notation, not
superscripts to fold).

Run over a listing they do real damage. Two seen in the corpus, both on
2026-09-23:

  * repair-math-spans merged forward through a listing looking for a closing
    \\), which changed which spans it joined a hundred lines earlier and left
    the prose with unbalanced math. LaTeXML then hit 101 errors and gave up on
    the whole document.
  * fold-unicode-scripts rewrote `∫₀` to `∫\\ensuremath{_{0}}` inside a Lean
    docstring, putting a math-mode macro inside verbatim.

Both were invisible until a listing was actually highlighted, because before
that the listings held little that these passes recognised.
"""
from __future__ import annotations

import re
from typing import Callable

# \begin{Shaded} wraps \begin{Highlighting}, so matching the outer environment
# consumes both. The others are listed for the cases pandoc emits directly.
PROTECTED = re.compile(
    r"\\begin\{(Shaded|Highlighting|verbatim|alltt|lstlisting)\}.*?\\end\{\1\}",
    re.S)


def map_outside_code(text: str,
                     fn: Callable[[str], tuple[str, int]]) -> tuple[str, int]:
    """Run fn on each stretch of prose, leaving listings byte-identical.

    fn takes a string and returns (rewritten, count); the counts are summed."""
    out, total, pos = [], 0, 0
    for m in PROTECTED.finditer(text):
        piece, n = fn(text[pos:m.start()])
        out.append(piece)
        out.append(m.group(0))
        total += n
        pos = m.end()
    piece, n = fn(text[pos:])
    out.append(piece)
    return "".join(out), total + n
