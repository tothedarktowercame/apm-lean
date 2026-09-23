#!/usr/bin/env python3
"""Revert any line whose math delimiters normalization left unparseable.

normalize-math-prose applies many independent rules to a line. When two of them
wrap overlapping text, the wraps collide and share a delimiter -- `|f(x)| > α`
becomes `$|f(x)| > $\\alpha$`, where the compare rule's closing `$` is the same
character as the one opening `$\\alpha$`. Every delimiter after the collision
then pairs with the wrong partner, so a single bad wrap corrupts the rest of the
line: pandoc emits literal `\\$` and drops the TeX commands into text mode.

Rather than chase each interaction, this pass checks the result. A normalized
line is accepted only if every `$...$` span on it satisfies pandoc's rules for
inline math:

  * an even number of unescaped `$`
  * a non-space character immediately right of each opening `$`
  * a non-space character immediately left of each closing `$`
  * no digit immediately after a closing `$`

If the normalized line fails and the original passed, the original is restored.
Nothing is lost by reverting: the bare Unicode in the original is handled by
pandoc-mathify.lua downstream, which is Unicode-aware. The guard only ever
trades a broken wrap for an unwrapped expression.

    guard-math-wellformed.py --before DIR --after DIR
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

FENCE = re.compile(r"^\s*(```|~~~)")


def dollar_positions(line: str) -> list[int]:
    out, i = [], 0
    while i < len(line):
        if line[i] == "\\":
            i += 2
            continue
        if line[i] == "$":
            out.append(i)
        i += 1
    return out


# Ordinary English words. A math span containing one is almost certainly the
# result of two wraps colliding and re-pairing across the prose between them.
PROSE_WORDS = {
    "a", "an", "and", "are", "as", "at", "be", "because", "but", "by", "can",
    "for", "from", "gives", "has", "have", "if", "in", "is", "it", "its", "of",
    "on", "or", "since", "so", "such", "that", "the", "then", "this", "to",
    "was", "we", "were", "when", "where", "which", "with", "definition",
    "measure", "positive", "converges", "implies", "follows", "every", "all",
}


def captures_prose(span: str) -> bool:
    """Does this span contain running English rather than mathematics?"""
    stripped = re.sub(r"\\[A-Za-z]+", " ", span)      # drop TeX commands
    stripped = re.sub(r"[^A-Za-z ]", " ", stripped)   # drop symbols and digits
    return any(w.lower() in PROSE_WORDS for w in stripped.split() if len(w) > 1)


def well_formed(line: str) -> bool:
    pos = dollar_positions(line)
    if len(pos) % 2:
        return False
    for a, b in zip(pos[0::2], pos[1::2]):
        if b == a + 1:
            return False                      # empty span
        if line[a + 1].isspace():
            return False                      # space after opening $
        if line[b - 1].isspace():
            return False                      # space before closing $
        if b + 1 < len(line) and line[b + 1].isdigit():
            return False                      # digit after closing $
        if captures_prose(line[a + 1 : b]):
            return False                      # span swallowed running prose
    return True


def guard(before: str, after: str) -> tuple[str, int]:
    b_lines, a_lines = before.split("\n"), after.split("\n")
    if len(b_lines) != len(a_lines):
        # Line counts diverged (rejoin ran between); cannot align, leave as is.
        return after, 0
    reverted = 0
    in_fence = False
    for i, (bl, al) in enumerate(zip(b_lines, a_lines)):
        if FENCE.match(al):
            in_fence = not in_fence
            continue
        if in_fence or "$$" in al:
            continue
        if bl == al:
            continue
        if not well_formed(al) and well_formed(bl):
            a_lines[i] = bl
            reverted += 1
    return "\n".join(a_lines), reverted


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--before", required=True)
    ap.add_argument("--after", required=True)
    args = ap.parse_args()

    total = files = 0
    for after_path in sorted(Path(args.after).glob("*.md")):
        before_path = Path(args.before) / after_path.name
        if not before_path.is_file():
            continue
        fixed, n = guard(
            before_path.read_text(encoding="utf-8", errors="replace"),
            after_path.read_text(encoding="utf-8", errors="replace"),
        )
        if n:
            total += n
            files += 1
            after_path.write_text(fixed, encoding="utf-8")
    print(f"Reverted {total} line(s) normalization left unparseable, in {files} file(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
