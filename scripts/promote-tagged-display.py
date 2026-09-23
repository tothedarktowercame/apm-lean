#!/usr/bin/env python3
"""Promote a tagged display to an equation environment.

amsmath's \\tag only works inside an equation environment. pandoc emits display
math as \\[ ... \\], so a source formula carrying its own tag --

    \\[a(u_n,v) = \\ell(v) \\qquad\\text{for all } v \\in V_n. \\tag{D_n}\\]

-- reaches LaTeX as \\tag inside \\[ \\], where it is an error and takes the rest
of the formula with it. Rewriting the delimiters keeps the tag and the numbering
the author asked for.

Operates on generated .tex; sources are never touched.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

# A display block that contains \tag somewhere inside it.
TAGGED = re.compile(r"\\\[((?:(?!\\\]).)*?\\tag\{(?:[^{}]|\{[^{}]*\})*\}(?:(?!\\\]).)*?)\\\]", re.S)


# \tag typesets its argument in text mode, so a tag like {D_n} or {A^*} is a
# subscript outside maths -- an error. Put such a tag in maths itself.
TAG_BODY = re.compile(r"\\tag\{((?:[^{}]|\{[^{}]*\})*)\}")


def mathify_tags(body: str) -> str:
    def repl(m: re.Match) -> str:
        inner = m.group(1)
        if ("_" in inner or "^" in inner) and "$" not in inner:
            return "\\tag{$" + inner + "$}"
        return m.group(0)
    return TAG_BODY.sub(repl, body)


def promote(text: str) -> tuple[str, int]:
    return TAGGED.subn(
        lambda m: "\\begin{equation}" + mathify_tags(m.group(1)) + "\\end{equation}",
        text,
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    total = files = 0
    for p in sorted(Path(x) for x in args.paths):
        src = p.read_text(encoding="utf-8", errors="replace")
        fixed, n = promote(src)
        if n:
            total += n
            files += 1
            if args.write:
                p.write_text(fixed, encoding="utf-8")
    print(f"Promoted {total} tagged display(s) to equation in {files} file(s)"
          + ("" if args.write else " (dry run)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
