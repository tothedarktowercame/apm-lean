#!/usr/bin/env python3
"""Restore the invariant that every LaTeX math span is brace-balanced.

pandoc-mathify.lua chooses math-span boundaries by token pattern without
tracking brace depth, so an expression like

    inf{M >= 0 : m({x : |f(x)| > M}) = 0}

is cut into \\(\\inf{M \\ge 0\\) : m(\\{x ... \\(> M}) = 0\\}, leaving a brace
group opened in one span and closed in another. That cannot compile.

The imbalance is usually not a missing brace at all. pandoc escapes the
opening set-brace as \\{ (a literal delimiter, which does not group) but leaves
its partner as a bare } (which does), so the pair never matches:

    \\inf{M \\ge 0 : m(\\{x : |f(x)| > M}) = 0}
                        ^^                  ^ literal open, grouping close

So this pass first re-pairs delimiters within each span: it walks the span
keeping a stack that records whether each opener was grouping ({) or literal
(\\{), and escapes any closer whose partner was literal. Only if a span is
still unbalanced after re-pairing does it merge forward, and it rewrites the
text-mode artifacts swept in (\\textbar -> |, stray \\$ -> nothing).

It is a repair, not a cure: the durable fix belongs in the filter's boundary
selection. Run check-math-span-balance.py afterwards to confirm the result.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

from texcode import map_outside_code

OPEN, CLOSE = r"\(", r"\)"

# Text-mode macros pandoc emits that are meaningless once inside math.
TEXT_ARTIFACTS = [
    (re.compile(r"\\textbar\{\}"), "|"),
    (re.compile(r"\\textbar\b"), "|"),
    (re.compile(r"\\textquotesingle\{\}"), "'"),
    (re.compile(r"\\textquotesingle\b"), "'"),
    (re.compile(r"\\\$"), ""),
    (re.compile(r"\\emph\{([^{}]*)\}"), r"\1"),
]


def brace_delta(s: str) -> int:
    depth, i = 0, 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        i += 1
    return depth


def repair_delimiters(s: str) -> tuple[str, int]:
    """Escape closers whose matching opener was a literal \\{ rather than a group."""
    out = []
    stack = []          # True if the opener was literal \\{
    fixes = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            nxt = s[i + 1]
            if nxt == "{":
                stack.append(True)
                out.append("\\{")
            elif nxt == "}":
                if stack:
                    stack.pop()
                out.append("\\}")
            else:
                out.append(s[i : i + 2])
            i += 2
            continue
        if c == "{":
            stack.append(False)
            out.append("{")
        elif c == "}":
            if stack and stack.pop():
                # Partner was a literal \\{ : this closer must be literal too.
                out.append("\\}")
                fixes += 1
            else:
                out.append("}")
        else:
            out.append(c)
        i += 1
    return "".join(out), fixes


def settled(s: str) -> bool:
    """Is this span balanced once literal/grouping delimiters are re-paired?"""
    return brace_delta(repair_delimiters(s)[0]) == 0


def clean_math(s: str) -> str:
    for pat, rep in TEXT_ARTIFACTS:
        s = pat.sub(rep, s)
    return s


def repair_prose(text: str) -> tuple[str, int]:
    """Merge unbalanced spans forward until balanced. Returns (text, n_repairs)."""
    out = []
    i = 0
    repairs = 0
    while True:
        a = text.find(OPEN, i)
        if a < 0:
            out.append(text[i:])
            break
        b = text.find(CLOSE, a + 2)
        if b < 0:
            out.append(text[i:])
            break

        out.append(text[i:a])
        body = text[a + 2 : b]
        end = b + 2

        if settled(body):
            body, dfix = repair_delimiters(body)
            repairs += 1 if dfix else 0
        elif True:
            # Absorb following material until the merged body balances. Each
            # absorbed \) .. \( boundary disappears, which is the point: the
            # expression was one piece of mathematics all along.
            merged = body
            cursor = end
            while not settled(merged):
                nxt_open = text.find(OPEN, cursor)
                nxt_close = text.find(CLOSE, cursor)
                if nxt_open < 0 or nxt_close < 0 or nxt_close < nxt_open:
                    break
                merged += text[cursor:nxt_open] + text[nxt_open + 2 : nxt_close]
                cursor = nxt_close + 2
            if settled(merged):
                body, _ = repair_delimiters(merged)
                end = cursor
                repairs += 1
            else:
                # Could not balance by merging; close the group explicitly
                # rather than emit something that cannot compile.
                d = brace_delta(body)
                body = body + ("}" * d if d > 0 else "")
                if d < 0:
                    body = ("{" * -d) + body
                repairs += 1

        out.append(OPEN + clean_math(body) + CLOSE)
        i = end
    return "".join(out), repairs


def repair(text: str) -> tuple[str, int]:
    """Prose only. A listing has no math spans, and letting the forward merge
    run into one changes which spans get joined far earlier in the file."""
    return map_outside_code(text, repair_prose)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()

    total = 0
    for p in sorted(Path(x) for x in args.paths):
        src = p.read_text()
        fixed, n = repair(src)
        if n:
            print(f"{p.name}: {n} span(s) repaired")
            total += n
            if args.write:
                p.write_text(fixed)
    print(f"\n{total} repairs" + ("" if args.write else " (dry run; pass --write)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
