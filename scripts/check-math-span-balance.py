#!/usr/bin/env python3
"""Report LaTeX that cannot compile: unbalanced delimiters inside math spans.

The First Proof checker suite catches prose/math style problems but not
structural ones, so a file that fails this check still passes those and only
fails at lualatex time, with an error pointing at a line rather than a cause.

Findings:
  brace-split-across-math  a \\( .. \\) span opens or closes a brace group it
                           does not finish -- the converter cut a math span in
                           the middle of \\inf{..}, \\{..\\} etc.
  escaped-dollar-in-math   a literal \\$ survived inside a math span
  textbar-in-math          \\textbar (a text macro) used inside math
  unclosed-math-span       odd number of \\( / \\) delimiters
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

MATH_SPAN = re.compile(r"\\\((.*?)\\\)", re.S)


def brace_delta(s: str) -> int:
    depth = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            # \{ and \} are literal braces, not grouping; skip any escaped char.
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        i += 1
    return depth


def check(path: Path) -> list[tuple[int, str, str]]:
    text = path.read_text()
    findings: list[tuple[int, str, str]] = []

    n_open = len(re.findall(r"\\\(", text))
    n_close = len(re.findall(r"\\\)", text))
    if n_open != n_close:
        findings.append((0, "unclosed-math-span",
                         f"{n_open} '\\(' vs {n_close} '\\)'"))

    for m in MATH_SPAN.finditer(text):
        body = m.group(1)
        line = text.count("\n", 0, m.start()) + 1
        d = brace_delta(body)
        if d != 0:
            sign = "opens" if d > 0 else "closes"
            findings.append((line, "brace-split-across-math",
                             f"span {sign} {abs(d)} unmatched brace: {body[:60]!r}"))
        if r"\$" in body:
            findings.append((line, "escaped-dollar-in-math", repr(body[:60])))
        if r"\textbar" in body:
            findings.append((line, "textbar-in-math", repr(body[:60])))
    return findings


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    args = ap.parse_args()

    total = 0
    bad_files = 0
    for p in sorted(Path(x) for x in args.paths):
        fs = check(p)
        if fs:
            bad_files += 1
        for line, kind, detail in fs:
            print(f"{p.name}:{line}: [{kind}] {detail}")
        total += len(fs)
    print(f"\nScanned {len(args.paths)} files | {bad_files} with findings | {total} findings")
    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
