#!/usr/bin/env python3
"""Rewrite LaTeX math delimiters into the ones pandoc's GFM reader understands.

Part of the corpus writes inline math as `\\(...\\)` and display math as
`\\[...\\]`. pandoc's `gfm` reader has no `tex_math_single_backslash`
extension -- it is rejected outright -- so it reads `\\(` as an escaped
parenthesis and the mathematics inside becomes prose: every command comes out
as `\\textbackslash mu`, `\\textbackslash le`, and so on.

`$...$` and `$$...$$` are what that reader does understand, and they are what
the rest of the corpus already uses, so this pass converts to them. It is a
pure delimiter swap; nothing between the delimiters is touched.

Fenced code blocks are skipped, so a literal `\\(` shown as an example stays
literal. Run on staged copies, before anything else looks at the math.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

FENCE = re.compile(r"^\s*(```|~~~)")
# Non-greedy, DOTALL: these spans may run across a line break -- but never
# across a blank line. Some files have more openers than closers (t97A04 has
# seven \[ and three \]), and without that limit the first unmatched opener
# pairs with a closer paragraphs away, swallowing prose into a display block
# and leaving a stray delimiter that makes TeX scan to end of file.
_NO_BLANK_LINE = r"(?:(?!\n[ \t]*\n).)*?"
# (?<!\\\\) so an escaped backslash is not taken for a delimiter: the text
# "\\\\[\u03b1]=(1,0)" is a literal backslash followed by the homology class
# [\u03b1], not the start of display math. Without this the false opener pairs
# with a closer paragraphs away and swallows the prose between them, leaving a
# stray $$ that makes TeX scan to end of file.
INLINE = re.compile(r"(?<!\\)\\\((" + _NO_BLANK_LINE + r")(?<!\\)\\\)", re.S)
DISPLAY = re.compile(r"(?<!\\)\\\[(" + _NO_BLANK_LINE + r")(?<!\\)\\\]", re.S)


def convert(text: str) -> tuple[str, int, int]:
    # Work block by block so fenced code is left alone.
    out: list[str] = []
    buf: list[str] = []
    in_fence = False
    n_inline = n_display = 0

    def flush() -> None:
        nonlocal n_inline, n_display
        if not buf:
            return
        chunk = "\n".join(buf)
        chunk, d = DISPLAY.subn(lambda m: f"$${m.group(1)}$$", chunk)
        chunk, i = INLINE.subn(lambda m: f"${m.group(1)}$", chunk)
        n_display += d
        n_inline += i
        out.append(chunk)
        buf.clear()

    for line in text.split("\n"):
        if FENCE.match(line):
            flush()
            in_fence = not in_fence
            out.append(line)
            continue
        if in_fence:
            out.append(line)
            continue
        buf.append(line)
    flush()
    return "\n".join(out), n_inline, n_display


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()

    ti = td = files = 0
    for p in sorted(Path(x) for x in args.paths):
        src = p.read_text(encoding="utf-8", errors="replace")
        fixed, i, d = convert(src)
        if i or d:
            files += 1
            ti += i
            td += d
            if args.write:
                p.write_text(fixed, encoding="utf-8")
    print(f"Converted {ti} inline and {td} display LaTeX delimiter pair(s) in {files} file(s)"
          + ("" if args.write else " (dry run)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
