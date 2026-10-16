#!/usr/bin/env python3
"""Rejoin inline math spans that a hard line wrap split in two.

Every `$...$` pair in the corpus is balanced at file level -- no file has an odd
count -- but 398 individual lines are odd, because the prose was hard-wrapped
through the middle of a formula:

    ... the norm $\\|f\\|_p \\le
    \\|f\\|_\\infty$ for all $p \\ge 1$ ...

pandoc does not read inline math across a newline, so it treats both `$` as
literal text, escapes them to `\\$`, and drops every TeX command between them
into text mode -- which is where `\\textbackslash le` in the output comes from.

This pass joins a line to its successor while the line's unescaped `$` count is
odd. It never joins across a blank line: a formula is not split by a paragraph
break, so an odd count that survives to a blank line is a real defect in the
source and is left alone to be reported rather than silently mangled.

Fenced code blocks and `$$` display blocks are skipped, matching the guards in
normalize-math-prose.py's process_file.

Run on staged copies only; sources are never mutated by the pipeline.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

DOLLAR = re.compile(r"(?<!\\)\$")
FENCE = re.compile(r"^\s*(```|~~~)")


def odd(line: str) -> bool:
    return len(DOLLAR.findall(line)) % 2 == 1


# NOTE: an earlier version of this pass also collapsed multi-line $$...$$
# blocks onto one line, to stop GFM reading a continuation line that begins
# "+ " as a bullet and breaking the block. It fixed 20 blocks and broke far
# more: several files carry a stray, unpaired $$, and joining from it pulls
# whole sections of prose into a single formula (121 -> 349 compile errors over
# the corpus). Gating on paragraph breaks and on file-level $$ parity did not
# make it safe, because the strays are paired-but-misplaced. The source needs
# repairing instead; see holes/ for the surviving cases.

LIST_MARKER = re.compile(r"^ {0,3}[-+*]\s")


def protect_display_continuations(text: str) -> tuple[str, int]:
    """Indent a line inside an open $$ display that markdown would read as a list item.

    A display continued on a line that begins "+ \\frac{h^4}{24}..." is read by
    GFM as a bullet: the formula is torn in two, and later passes cut the
    pieces into spans with unbalanced braces (m94A01 stopped compiling). Joining
    the lines broke more than it fixed (see the note above), so no text moves
    here: four spaces of indent make the line a paragraph continuation, which a
    list cannot interrupt. Only within one paragraph, and only while that
    paragraph has an odd number of $$ so far.
    """
    out, opened, fixed = [], 0, 0
    for line in text.split("\n"):
        if not line.strip():
            opened = 0
        elif opened % 2 == 1 and LIST_MARKER.match(line):
            line = "    " + line.lstrip()
            fixed += 1
        opened += line.count("$$")
        out.append(line)
    return "\n".join(out), fixed


def rejoin(text: str) -> tuple[str, int, int]:
    lines = text.split("\n")
    out: list[str] = []
    joins = 0
    abandoned = 0
    i = 0
    in_fence = False

    while i < len(lines):
        line = lines[i]

        if FENCE.match(line):
            in_fence = not in_fence
            out.append(line)
            i += 1
            continue
        if in_fence or "$$" in line:
            out.append(line)
            i += 1
            continue

        if not odd(line):
            out.append(line)
            i += 1
            continue

        # Pull in following lines until the span closes.
        merged = line
        j = i + 1
        while j < len(lines) and odd(merged):
            nxt = lines[j]
            if not nxt.strip() or FENCE.match(nxt) or "$$" in nxt:
                break
            merged = merged.rstrip() + " " + nxt.lstrip()
            j += 1

        if odd(merged):
            # Never closed before a paragraph break: leave the source untouched.
            abandoned += 1
            out.append(line)
            i += 1
        else:
            joins += j - i - 1
            out.append(merged)
            i = j

    return "\n".join(out), joins, abandoned


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()

    tj = ta = files = 0
    for p in sorted(Path(x) for x in args.paths):
        src = p.read_text(encoding="utf-8", errors="replace")
        fixed, joins, abandoned = rejoin(src)
        fixed, protected = protect_display_continuations(fixed)
        joins += protected
        if joins or abandoned:
            files += 1
            tj += joins
            ta += abandoned
            if args.write and joins:
                p.write_text(fixed, encoding="utf-8")
    print(f"Rejoined {tj} split math span(s) in {files} file(s)"
          + (f"; {ta} left unclosed at a paragraph break" if ta else "")
          + ("" if args.write else " (dry run)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
