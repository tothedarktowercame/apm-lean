"""Read a Lean source file as a list of top-level declarations.

Shared by render-lean-proofs.py (which sets each declaration as its own
listing) and annotate-lean-links.py (which links names in the informal proof to
the declarations that use them). Both need the same two facts about a file:
where its declarations begin, and which names each one mentions.
"""
from __future__ import annotations

import re

DECL_KINDS = (
    "theorem|lemma|def|abbrev|instance|structure|class|inductive|example|"
    "axiom|opaque"
)
MODIFIERS = r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
# A top-level declaration starts in column 0. Anything indented is inside a
# proof -- `have`, a nested `def` in a `let rec`, a tactic block.
DECL_START = re.compile(rf"^(?:@\[[^\]]*\]\s*)?{MODIFIERS}({DECL_KINDS})\s+([^\s:({{\[]+)")
DOC_START = re.compile(r"^/--")
ATTR_START = re.compile(r"^@\[")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*")

SORRY = re.compile(r"(?<![\w.'])sorry(?![\w'])")
CROSSREFS = re.compile(
    r"^\s*\*\*Mathlib cross-refs?:?\*\*\s*(.+?)$", re.M | re.I)


def segment(lines: list[str]) -> list[dict]:
    """Cut a Lean file into a header plus one chunk per top-level declaration.

    A chunk opens at a column-0 docstring, attribute or declaration keyword and
    runs to the next one, so a declaration keeps its own docstring, attributes
    and proof body together."""
    starts = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if DOC_START.match(line) or ATTR_START.match(line) or DECL_START.match(line):
            # A docstring or attribute opens the chunk its declaration belongs
            # to; do not open a second chunk at the declaration itself.
            if not starts or starts[-1][1] < i:
                starts.append((i, i))
            j = i
            # Advance past the docstring/attribute to find the declaration name.
            while j < len(lines) and not DECL_START.match(lines[j]):
                j += 1
                if j - i > 60:       # runaway: treat the opener as the chunk
                    break
            starts[-1] = (starts[-1][0], j)
            i = j + 1
            continue
        i += 1

    chunks = []
    if not starts:
        return [{"name": None, "kind": None, "lines": lines}]
    if starts[0][0] > 0:
        chunks.append({"name": None, "kind": None, "lines": lines[: starts[0][0]]})
    for n, (begin, declline) in enumerate(starts):
        end = starts[n + 1][0] if n + 1 < len(starts) else len(lines)
        m = DECL_START.match(lines[declline]) if declline < len(lines) else None
        chunks.append({
            "kind": m.group(1) if m else None,
            "name": m.group(2) if m else None,
            "lines": lines[begin:end],
        })
    return chunks



def docstring(chunk: dict) -> str | None:
    """The declaration's own /-- .. -/ docstring, as one line of prose.

    2,891 of the corpus's 6,730 declarations carry one, written in English by
    whoever formalised the proof -- the closest thing to a concept mapping that
    already exists in the repo."""
    text = "\n".join(chunk["lines"])
    m = re.match(r"\s*/--(.*?)-/", text, re.S)
    if not m:
        return None
    return " ".join(m.group(1).split())


# A name on one of these lines is part of the file's scaffolding, not a step of
# the argument; linking prose to "import Mathlib.Order.Filter.Basic" says
# nothing a reader wants in the margin.
STRUCTURAL = re.compile(r"^\s*(import|open|set_option|namespace|end|variable|universe)\b")


def uses(chunks: list[dict]) -> dict[str, list[str]]:
    """name -> the declarations that mention it, in file order.

    Exact: a token match, not a resolution. A name that only ever appears on an
    import or open line is omitted."""
    out: dict[str, list[str]] = {}
    for chunk in chunks:
        if not chunk["name"]:
            continue
        seen = set()
        for line in chunk["lines"]:
            if STRUCTURAL.match(line):
                continue
            for tok in IDENT.findall(line):
                if tok in seen:
                    continue
                seen.add(tok)
                out.setdefault(tok, []).append(chunk["name"])
    return out
