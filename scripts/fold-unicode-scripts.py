#!/usr/bin/env python3
"""Fold runs of Unicode super/subscript characters into one TeX script.

apm-unicode-math.sty maps each Unicode superscript to its own `^{..}`, which is
right for a single character and wrong for a run: `z¹²` becomes `z^{1}^{2}`,
a double superscript, which is a TeX error. Runs have to be folded before the
per-character mapping ever sees them.

This pass rewrites each maximal run into a single `^{...}` or `_{...}`, so `z¹²`
becomes `z^{12}` and `xₙ₊₁` becomes `x_{n+1}`. Runs of length one are folded
too, which makes the .sty mappings for these characters redundant but harmless.

Operates on generated .tex; sources are never touched.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

SUPER = {
    "⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4", "⁵": "5", "⁶": "6",
    "⁷": "7", "⁸": "8", "⁹": "9", "⁺": "+", "⁻": "-", "⁼": "=", "⁽": "(",
    "⁾": ")", "ⁿ": "n", "ⁱ": "i", "ᵐ": "m", "ᶜ": "c", "ˣ": "x", "ᵏ": "k",
    "ᵃ": "a", "ᵇ": "b", "ᵈ": "d", "ᵉ": "e", "ᵍ": "g", "ʰ": "h", "ʲ": "j",
    "ˡ": "l", "ᵒ": "o", "ᵖ": "p", "ʳ": "r", "ˢ": "s", "ᵗ": "t", "ᵘ": "u",
    "ᵛ": "v", "ʷ": "w", "ʸ": "y", "ᶻ": "z",
}
SUB = {
    "₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4", "₅": "5", "₆": "6",
    "₇": "7", "₈": "8", "₉": "9", "₊": "+", "₋": "-", "₌": "=", "₍": "(",
    "₎": ")", "ₐ": "a", "ₑ": "e", "ₕ": "h", "ᵢ": "i", "ⱼ": "j", "ₖ": "k",
    "ₗ": "l", "ₘ": "m", "ₙ": "n", "ₒ": "o", "ₚ": "p", "ᵣ": "r", "ₛ": "s",
    "ₜ": "t", "ᵤ": "u", "ᵥ": "v", "ₓ": "x",
}

SUPER_RUN = re.compile(f"[{''.join(SUPER)}]+")
SUB_RUN = re.compile(f"[{''.join(SUB)}]+")


def fold(text: str) -> tuple[str, int]:
    n = 0

    def sup(m: re.Match) -> str:
        nonlocal n
        n += 1
        return "\\ensuremath{^{" + "".join(SUPER[c] for c in m.group(0)) + "}}"

    def sup_with_prime(m: re.Match) -> str:
        # A prime straight after a superscript is a second superscript --
        # "g\u207b\u00b9' C" becomes g^{-1}' , which TeX refuses. Fold the prime into
        # the same group.
        nonlocal n
        n += 1
        body = "".join(SUPER[c] for c in m.group(1)) + "\\prime" * len(m.group(2))
        return "\\ensuremath{^{" + body + "}}"

    def sub(m: re.Match) -> str:
        nonlocal n
        n += 1
        return "\\ensuremath{_{" + "".join(SUB[c] for c in m.group(0)) + "}}"

    text = re.sub(f"([{''.join(SUPER)}]+)('+)", sup_with_prime, text)
    text = SUPER_RUN.sub(sup, text)
    text = SUB_RUN.sub(sub, text)
    return text, n


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    total = files = 0
    for p in sorted(Path(x) for x in args.paths):
        src = p.read_text(encoding="utf-8", errors="replace")
        fixed, n = fold(src)
        if n:
            total += n
            files += 1
            if args.write:
                p.write_text(fixed, encoding="utf-8")
    print(f"Folded {total} Unicode script run(s) in {files} file(s)"
          + ("" if args.write else " (dry run)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
