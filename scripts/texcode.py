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
CODE_ENVS = ("Shaded", "Highlighting", "verbatim", "alltt", "lstlisting")

# Tables are prose-adjacent but not prose: a cell is not part of the reading
# column, so a Tufte sidenote anchored in one starts at the table's right edge
# and runs off the page. Passes that place marginal material exclude them too.
TABLE_ENVS = ("longtable", "tabular", "tabularx", "array")


def _envs(names: tuple[str, ...], tag: str) -> str:
    """An alternation matching any of these environments, start to end.

    Each alternative carries its own NAMED group for the back-reference. Numbered
    groups do not survive being concatenated into a larger alternation -- the \\1
    in the second branch silently starts referring to the first branch's group,
    and that branch then never matches. Which is how tables went on being
    annotated after they were supposedly excluded."""
    return (rf"\\begin\{{(?P<{tag}>" + "|".join(names) + r")\*?\}.*?"
            rf"\\end\{{(?P={tag})\*?\}}")


PROTECTED = re.compile(_envs(CODE_ENVS, "code"), re.S)
CODE_OR_TABLE = re.compile(
    _envs(CODE_ENVS, "code") + "|" + _envs(TABLE_ENVS, "table"), re.S)


def map_outside_code(text: str,
                     fn: Callable[[str], tuple[str, int]],
                     protect: re.Pattern = PROTECTED) -> tuple[str, int]:
    """Run fn on each stretch of prose, leaving protected regions byte-identical.

    fn takes a string and returns (rewritten, count); the counts are summed."""
    out, total, pos = [], 0, 0
    for m in protect.finditer(text):
        piece, n = fn(text[pos:m.start()])
        out.append(piece)
        out.append(m.group(0))
        total += n
        pos = m.end()
    piece, n = fn(text[pos:])
    out.append(piece)
    return "".join(out), total + n
