#!/usr/bin/env python3
"""Check that a markdown rewrite changed only how mathematics is written.

The informal solutions write much of their mathematics as Unicode prose
("f\\_k = n · 1\\_{[j/n, (j+1)/n]}", "∃ε>0: ∀N>0"), which the TeX converter has to
guess at. Rewriting it as $...$ LaTeX removes the guessing, but these files are
the record other people work from, so a rewrite must not change one word or
symbol of the content. This reduces both versions to one canonical spelling --
LaTeX commands and Unicode symbols to the same token, sub/superscripts to _x and
^x, markdown escapes undone, braces, $ and spacing dropped -- and compares them
character by character. Fenced code blocks must be byte-identical.

Usage:
  check-math-markup.py <problem-id>...        compare against git HEAD
  check-math-markup.py --old A.md --new B.md
Exit status is non-zero when any file differs in content; each difference is
printed with context.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# One token per symbol, whichever way it is written.
SYMBOLS = {
    "∀": "forall", "∃": "exists", "∄": "nexists", "∈": "in", "∉": "notin", "∋": "ni",
    "⊂": "subset", "⊆": "subseteq", "⊊": "subsetneq", "⊃": "supset", "⊇": "supseteq",
    "∪": "cup", "∩": "cap", "⋃": "bigcup", "⋂": "bigcap", "∖": "setminus", "∅": "emptyset",
    "≤": "le", "≥": "ge", "≠": "ne", "≈": "approx", "≅": "cong", "≃": "simeq", "≡": "equiv",
    "∼": "sim", "~": "sim", "∝": "propto", "≪": "ll", "≫": "gg", "≺": "prec", "≻": "succ",
    "→": "to", "←": "leftarrow", "↦": "mapsto", "⟶": "longrightarrow", "↪": "hookrightarrow",
    "⇒": "Rightarrow", "⟹": "Longrightarrow", "⟸": "Longleftarrow", "⇐": "Leftarrow",
    "⇔": "Leftrightarrow", "⟺": "Longleftrightarrow", "↔": "leftrightarrow", "↑": "uparrow",
    "↓": "downarrow", "↗": "nearrow", "↘": "searrow", "⇀": "rightharpoonup", "↠": "twoheadrightarrow",
    "∞": "infty", "∑": "sum", "∏": "prod", "∫": "int", "∮": "oint", "∬": "iint", "∂": "partial",
    "∇": "nabla", "√": "sqrt", "±": "pm", "∓": "mp", "×": "times", "·": "cdot", "⋅": "cdot",
    "∘": "circ", "⊗": "otimes", "⊕": "oplus", "⊥": "perp", "∥": "parallel", "∧": "wedge",
    "∨": "vee", "¬": "neg", "⊢": "vdash", "⊨": "models", "†": "dagger", "⋆": "star", "∗": "ast",
    "ℵ": "aleph", "ℓ": "ell", "ℏ": "hbar", "℘": "wp", "⟨": "langle", "⟩": "rangle",
    "⌊": "lfloor", "⌋": "rfloor", "⌈": "lceil", "⌉": "rceil", "‖": "|", "…": "dots", "⋯": "dots",
    "⋮": "vdots", "⋱": "ddots", "′": "'", "″": "''", "−": "-", "–": "-", "∣": "|", "◦": "circ",
    "□": "square", "■": "blacksquare", "∎": "blacksquare", "★": "star", "♯": "sharp", "♭": "flat",
    "ℝ": "R", "ℂ": "C", "ℕ": "N", "ℤ": "Z", "ℚ": "Q", "𝔽": "F", "ℍ": "H", "ℙ": "P", "𝕋": "T",
    "α": "alpha", "β": "beta", "γ": "gamma", "δ": "delta", "ε": "epsilon", "ϵ": "epsilon",
    "ζ": "zeta", "η": "eta", "θ": "theta", "ϑ": "theta", "ι": "iota", "κ": "kappa",
    "λ": "lambda", "μ": "mu", "ν": "nu", "ξ": "xi", "π": "pi", "ρ": "rho", "ϱ": "rho",
    "σ": "sigma", "ς": "sigma", "τ": "tau", "υ": "upsilon", "φ": "phi", "ϕ": "phi", "χ": "chi",
    "ψ": "psi", "ω": "omega", "Γ": "Gamma", "Δ": "Delta", "Θ": "Theta", "Λ": "Lambda",
    "Ξ": "Xi", "Π": "Pi", "Σ": "sum", "Υ": "Upsilon", "Φ": "Phi", "Ψ": "Psi", "Ω": "Omega",
    "ℒ": "mathcalL", "ℱ": "mathcalF", "ℋ": "mathcalH", "ℬ": "mathcalB", "𝒜": "mathcalA",
}
BLACKBOARD = {"ℝ": "R", "ℂ": "C", "ℕ": "N", "ℤ": "Z", "ℚ": "Q", "𝔽": "F", "ℍ": "H", "ℙ": "P",
              "𝕋": "T", "𝟙": "1"}
# LaTeX spellings that differ from the token above.
ALIASES = {
    "leq": "le", "geq": "ge", "neq": "ne", "varepsilon": "epsilon", "vartheta": "theta",
    "varphi": "phi", "varrho": "rho", "varsigma": "sigma", "rightarrow": "to", "gets": "leftarrow",
    "implies": "Longrightarrow", "impliedby": "Longleftarrow", "iff": "Longleftrightarrow",
    "lnot": "neg", "land": "wedge", "lor": "vee", "ldots": "dots", "cdots": "dots", "dots": "dots",
    "dotsc": "dots", "dotsb": "dots", "lVert": "|", "rVert": "|", "Vert": "|", "|": "|", "vert": "|",
    "lvert": "|", "rvert": "|", "mid": "|", "qed": "blacksquare", "Box": "square",
    "Sigma": "sum", "colon": ":", "prime": "'", "ast": "ast", "smallsetminus": "setminus", "varnothing": "emptyset",
    "to": "to", "le": "le", "ge": "ge", "ne": "ne", "limsup": "limsup", "liminf": "liminf",
}
SUPER = dict(zip("⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁿⁱᵏᵀ", "0123456789+-=()nikT"))
SUB = dict(zip("₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₒₓₕₖₗₘₙₚₛₜᵢⱼ", "0123456789+-=()aeoxhklmnpstij"))
FONT = re.compile(r"\\(?:mathbb|mathbf|mathrm|mathit|mathsf|mathtt|operatorname|text|textrm|"
                  r"textit|textbf|emph|boldsymbol|bm|mbox|mathscr|mathfrak)\b")
CAL = re.compile(r"\\mathcal\s*\{?\s*([A-Za-z])\s*\}?")
SPACING = re.compile(r"\\[,;:! ]|\\(?:quad|qquad|left|right|big|Big|bigg|Bigg|bigl|bigr|Bigl|Bigr|"
                     r"displaystyle|textstyle|limits|nolimits)(?![A-Za-z])")
FENCE = re.compile(r"```.*?```", re.S)


def unicode_tokens(s: str) -> str:
    out = []
    for ch in s:
        if ch in SUPER:
            out.append("^" + SUPER[ch])
        elif ch in SUB:
            out.append("_" + SUB[ch])
        elif ch in BLACKBOARD:
            out.append(BLACKBOARD[ch])            # \mathbb{R} drops its font to a plain R too
        elif ch in SYMBOLS:
            out.append("\x01" + SYMBOLS[ch] + "\x02")
        else:
            out.append(ch)
    return "".join(out)


def latex_tokens(s: str) -> str:
    s = CAL.sub(lambda m: "\\mathcal" + m.group(1), s)
    s = SPACING.sub(" ", s)
    s = FONT.sub("", s)
    s = re.sub(r"\\(lim|limsup|liminf|sup|inf|max|min|log|ln|exp|sin|cos|tan|det|dim|ker|deg|"
               r"gcd|arg|Re|Im|mod|bmod|pmod)(?![A-Za-z])", r"\1", s)
    s = re.sub(r"\\mathcal([A-Za-z])", lambda m: "\x01mathcal" + m.group(1) + "\x02", s)
    s = re.sub(r"\\([A-Za-z]+)", lambda m: "\x01" + ALIASES.get(m.group(1), m.group(1)) + "\x02", s)
    s = re.sub(r"\\([{}|_#&%$])", r"\1", s)
    return s


def canon(text: str) -> str:
    text = FENCE.sub("", text)
    text = re.sub(r"\\([_*\[\]#`|<>~])", r"\1", text)          # markdown escapes
    text = text.replace("...", "…")
    text = unicode_tokens(latex_tokens(text))
    text = text.replace("lim\x01sup", "limsup").replace("lim\x01inf", "liminf")
    text = re.sub(r"lim\s*sup", "limsup", text)
    text = re.sub(r"lim\s*inf", "liminf", text)
    text = re.sub(r"[\s${}*`]", "", text)          # spacing, delimiters, grouping, emphasis, code
    text = re.sub(r"\x01sqrt\x02\(([^()]*)\)", "\x01sqrt\x02\\1", text)   # √(2k) is \\sqrt{2k}
    return text


def fences(text: str) -> list[str]:
    return FENCE.findall(text)


def compare(old: str, new: str, label: str) -> bool:
    ok = True
    if fences(old) != fences(new):
        print(f"{label}: a fenced code block changed")
        ok = False
    a, b = canon(old), canon(new)
    if a != b:
        i = next((k for k in range(min(len(a), len(b))) if a[k] != b[k]), min(len(a), len(b)))
        show = lambda s: s[max(0, i - 50):i + 50].replace("\x01", "\\").replace("\x02", "")
        print(f"{label}: content differs at canonical offset {i}")
        print(f"   old: …{show(a)}…")
        print(f"   new: …{show(b)}…")
        ok = False
    return ok


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("ids", nargs="*")
    ap.add_argument("--old")
    ap.add_argument("--new")
    args = ap.parse_args()
    if args.old and args.new:
        return 0 if compare(Path(args.old).read_text(), Path(args.new).read_text(), args.new) else 1
    bad = 0
    for pid in args.ids:
        rel = f"problems/{pid}/informal-solution.md"
        old = subprocess.run(["git", "-C", str(ROOT), "show", f"HEAD:{rel}"],
                             capture_output=True, text=True, check=True).stdout
        new = (ROOT / rel).read_text()
        if not compare(old, new, pid):
            bad += 1
    print(f"{len(args.ids) - bad}/{len(args.ids)} unchanged in content")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
