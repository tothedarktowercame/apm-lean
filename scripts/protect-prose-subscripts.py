#!/usr/bin/env python3
"""Escape bare '_' left in prose so GFM does not read subscripts as emphasis.

The APM Lean informal proofs write subscripts as bare underscores in running
text ("‖f‖_p ≤ ‖f‖_∞"). GitHub-flavoured Markdown reads the two underscores as
a matched emphasis pair, so pandoc emits

    ‖f‖\\emph{p ≤ ‖f‖}∞

which silently changes the mathematics: two subscripts become one italic run.
The First Proof corpus never hit this because its markdown has the underscores
hand-escaped already.

Run this AFTER normalize-math-prose.py, so genuine subscripts have been lifted
into $...$ first and only the residue is escaped. Code spans, fenced blocks and
math spans are left untouched.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

FENCE = re.compile(r"^\s*(```|~~~)")
# Inline code, display math, inline math -- regions whose content is verbatim.
# A code span is delimited by backtick runs of EQUAL length (CommonMark). This
# matters here because normalize-math-prose.py rewrites smart quotes into TeX
# quotes (``like this''), putting stray backtick runs into the Markdown; a
# regex that pairs any run with any other run then mistakes the gap between a
# quote and a real code span for code, and escapes the identifier inside it.
PROTECTED = re.compile(
    r"((?<!`)(`+)(?:(?!\2)[\s\S])*?\2(?!`)|\$\$.*?\$\$|\$[^$\n]*\$)", re.S
)


def escape_segment(s: str) -> tuple[str, int]:
    out, n = [], 0
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            out.append(s[i : i + 2])
            i += 2
            continue
        if c == "_":
            # A subscript has a base: "f_n", "|x|_2", "(a)_k". An underscore
            # with whitespace or a line start before it is a Markdown emphasis
            # marker, and escaping it turns the author's italics into literal
            # underscores -- which the mathifier then reads as a subscript with
            # no base. Leave those alone.
            prev = out[-1][-1] if out and out[-1] else ""
            # Unicode closers count too: "‖f‖_p" was still read as emphasis
            # (2026-10-15: 77 files) because ‖ is not alphanumeric.
            if prev and (prev.isalnum() or prev in ")]}|‖⟩⟫′'*"):
                out.append(r"\_")
                n += 1
            else:
                out.append(c)
        else:
            out.append(c)
        i += 1
    return "".join(out), n


def process(text: str) -> tuple[str, int]:
    lines = text.split("\n")
    in_fence = False
    in_display = False
    total = 0
    for idx, line in enumerate(lines):
        if FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        # Display math routinely spans several lines, so it has to be tracked
        # across them: a "_" inside $$..$$ is a subscript and must not be
        # escaped. A line carrying an odd number of "$$" toggles the state.
        fences_here = line.count("$$")
        if in_display:
            if fences_here % 2:
                in_display = False
            continue
        if fences_here % 2:
            in_display = True
            continue
        # Two capture groups, so split() yields text, whole, inner, text, ...
        # The inner group only exists to length-match the backtick run; emitting
        # it would duplicate those backticks, so it is dropped on rejoin.
        pieces = PROTECTED.split(line)
        rebuilt = []
        for j, piece in enumerate(pieces):
            if j % 3 == 2:
                continue
            if piece is None:
                continue
            if j % 3 == 0:
                piece, n = escape_segment(piece)
                total += n
            rebuilt.append(piece)
        lines[idx] = "".join(rebuilt)
    return "\n".join(lines), total


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()

    total = 0
    for p in sorted(Path(x) for x in args.paths):
        src = p.read_text()
        fixed, n = process(src)
        if n:
            total += n
            if args.write:
                p.write_text(fixed)
    print(f"Escaped {total} prose underscore(s)" + ("" if args.write else " (dry run)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
