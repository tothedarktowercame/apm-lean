#!/usr/bin/env python3
"""Make inline math spans satisfy pandoc's rules for `$...$`.

pandoc reads `$...$` as math only when the opening `$` has a non-space character
immediately to its right, the closing `$` has a non-space immediately to its
left, and the closing `$` is not followed by a digit. A span that breaks any of
these is left as literal text: both delimiters come out as `\\$`, every TeX
command inside lands in text mode, and -- worse -- the delimiters after it on
the line pair up against the wrong partners, so one bad span corrupts the rest
of the line.

normalize-math-prose produces such spans, e.g. `$|f(x)| > $` (trailing space
inside the wrap) sitting directly against `$\\alpha$`. This pass walks each
line pairing delimiters in order and moves offending whitespace outside the
wrap, which is meaning-preserving: space inside math mode is not typeset.

Run on staged copies after normalization and before pandoc.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

FENCE = re.compile(r"^\s*(```|~~~)")


def split_dollars(line: str) -> list[int]:
    """Indices of unescaped '$' in the line."""
    out, i = [], 0
    while i < len(line):
        if line[i] == "\\":
            i += 2
            continue
        if line[i] == "$":
            out.append(i)
        i += 1
    return out


def tidy_line(line: str) -> tuple[str, int]:
    pos = split_dollars(line)
    if len(pos) < 2 or len(pos) % 2:
        return line, 0

    pieces, fixes, prev = [], 0, 0
    for a, b in zip(pos[0::2], pos[1::2]):
        pieces.append(line[prev:a])
        body = line[a + 1 : b]
        stripped = body.strip()
        if not stripped:
            # An empty wrap is not math at all; drop the delimiters.
            pieces.append(body)
            fixes += 1
        elif stripped != body:
            lead = body[: len(body) - len(body.lstrip())]
            trail = body[len(body.rstrip()) :]
            pieces.append(f"{lead}${stripped}${trail}")
            fixes += 1
        else:
            pieces.append(f"${body}$")
        prev = b + 1
    pieces.append(line[prev:])
    return "".join(pieces), fixes


def tidy(text: str) -> tuple[str, int]:
    lines = text.split("\n")
    in_fence = False
    total = 0
    for i, line in enumerate(lines):
        if FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence or "$$" in line:
            continue
        lines[i], n = tidy_line(line)
        total += n
    return "\n".join(lines), total


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()

    total = files = 0
    for p in sorted(Path(x) for x in args.paths):
        src = p.read_text(encoding="utf-8", errors="replace")
        fixed, n = tidy(src)
        if n:
            total += n
            files += 1
            if args.write:
                p.write_text(fixed, encoding="utf-8")
    print(f"Tidied {total} math delimiter(s) in {files} file(s)"
          + ("" if args.write else " (dry run)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
