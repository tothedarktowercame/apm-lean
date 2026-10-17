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
import unicodedata
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
    "⇒": "implies", "⟹": "implies", "⟸": "impliedby", "⇐": "impliedby",
    "⇔": "iff", "⟺": "iff", "↔": "leftrightarrow", "↑": "uparrow",
    "↓": "downarrow", "↗": "nearrow", "↘": "searrow", "⇀": "rightharpoonup", "↠": "twoheadrightarrow",
    "∞": "infty", "∑": "sum", "∏": "prod", "∫": "int", "∮": "oint", "∬": "iint", "∂": "partial",
    "∇": "nabla", "√": "sqrt", "±": "pm", "∓": "mp", "×": "times", "·": "cdot", "⋅": "cdot",
    "∘": "circ", "⊗": "otimes", "⊕": "oplus", "⊥": "perp", "∥": "parallel", "∧": "wedge",
    "∨": "vee", "¬": "neg", "⊢": "vdash", "⊨": "models", "†": "dagger", "⋆": "star", "∗": "ast",
    "⊤": "top", "⟂": "perp", "↛": "nto", "÷": "div", "∭": "iiint", "≢": "notequiv", "µ": "mu", "⇏": "nRightarrow", "⋊": "rtimes", "⋉": "ltimes", "≲": "lesssim", "≳": "gtrsim", "⊊": "subsetneq", "⊋": "supsetneq", "½": "1/2", "△": "triangle", "°": "circ", "∆": "Delta", "ℵ": "aleph", "ℓ": "ell", "ℏ": "hbar", "℘": "wp", "⟨": "langle", "⟩": "rangle",
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
BLACKBOARD = {chr(0x1D538 + i): chr(65 + i) for i in range(26)}
BLACKBOARD.update({"ℝ": "R", "ℂ": "C", "ℕ": "N", "ℤ": "Z", "ℚ": "Q", "𝔽": "F", "ℍ": "H", "ℙ": "P",
              "𝕋": "T", "𝟙": "1"})
# LaTeX spellings that differ from the token above.
ALIASES = {
    "leq": "le", "geq": "ge", "neq": "ne", "varepsilon": "epsilon", "vartheta": "theta",
    "varphi": "phi", "varrho": "rho", "varsigma": "sigma", "rightarrow": "to", "gets": "leftarrow",
    "implies": "implies", "impliedby": "impliedby", "iff": "iff", "Rightarrow": "implies",
    "Longrightarrow": "implies", "Leftarrow": "impliedby", "Longleftarrow": "impliedby",
    "Leftrightarrow": "iff", "Longleftrightarrow": "iff",
    "lnot": "neg", "land": "wedge", "lor": "vee", "ldots": "dots", "cdots": "dots", "dots": "dots",
    "dotsc": "dots", "dotsb": "dots", "lVert": "|", "rVert": "|", "Vert": "|", "|": "|", "vert": "|",
    "lvert": "|", "rvert": "|", "mid": "|", "qed": "blacksquare", "Box": "square",
    "Sigma": "sum", "bar": "overline", "widehat": "hat", "widetilde": "tilde", "colon": ":", "prime": "'", "ast": "ast", "smallsetminus": "setminus", "varnothing": "emptyset",
    "to": "to", "le": "le", "ge": "ge", "ne": "ne", "limsup": "limsup", "liminf": "liminf",
}
SUPER = dict(zip("⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁿⁱᵏᵀᵃᵇᶜᵈᵉᶠᵍʰʲˡᵐᵒᵖʳˢᵗᵘᵛʷˣʸᶻ", "0123456789+-=()nikTabcdefghjlmoprstuvwxyz"))
SUPER.update({"ᵅ": "α", "ᵝ": "β", "ˣ": "x", "ʸ": "y", "ᵍ": "g", "ᴴ": "H", "ᴺ": "N"})
COMBINING = {"\u030c": "check", "\u0304": "overline", "\u0305": "overline", "\u0302": "hat", "\u0303": "tilde", "\u0307": "dot"}
SUB = dict(zip("₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₒₓₕₖₗₘₙₚₛₜᵢⱼ", "0123456789+-=()aeoxhklmnpstij"))
FONT = re.compile(r"\\(?:mathbb|mathbf|mathrm|mathit|mathsf|mathtt|operatorname|text|textrm|"
                  r"textit|textbf|emph|boldsymbol|bm|mbox|mathscr|mathfrak)\b")
CAL = re.compile(r"\\mathcal\s*\{?\s*([A-Za-z])\s*\}?")
SPACING = re.compile(r"\\[,;:! ]|\\(?:quad|qquad|left|right|big|Big|bigg|Bigg|bigl|bigr|Bigl|Bigr|"
                     r"displaystyle|textstyle|limits|nolimits)(?![A-Za-z])")
FENCE = re.compile(r"```.*?```", re.S)


SCRIPT = {chr(0x1D49C + i): "mathcal" + chr(65 + i) for i in range(26)}
SCRIPT.update({"ℬ": "mathcalB", "ℰ": "mathcalE", "ℱ": "mathcalF", "ℋ": "mathcalH", "ℐ": "mathcalI",
               "ℒ": "mathcalL", "ℳ": "mathcalM", "ℛ": "mathcalR"})
SYMBOLS.update(SCRIPT)


def unicode_tokens(s: str) -> str:
    # a run of super/subscripts is one exponent or index: f⁻¹ is f^{-1}
    s = re.sub("[" + "".join(SUPER) + "]+", lambda m: "^" + "".join(SUPER[c] for c in m.group(0)), s)
    s = re.sub("[" + "".join(SUB) + "]+", lambda m: "_" + "".join(SUB[c] for c in m.group(0)), s)
    # D̄ is \overline{D}: the accent token goes before its letter, as in LaTeX
    s = re.sub("(.)([" + "".join(COMBINING) + "])", lambda m: "\x01" + COMBINING[m.group(2)] + "\x02" + m.group(1), s)
    out = []
    for ch in s:
        if False:
            pass
        elif ch in BLACKBOARD:
            out.append(BLACKBOARD[ch])            # \mathbb{R} drops its font to a plain R too
        elif ch in SYMBOLS:
            v = SYMBOLS[ch]
            out.append("\x01" + v + "\x02" if v[:1].isalpha() else v)   # − is -, ′ is ', ‖ is |
        else:
            out.append(ch)
    return "".join(out)


def latex_tokens(s: str) -> str:
    s = CAL.sub(lambda m: "\\mathcal" + m.group(1), s)
    s = SPACING.sub(" ", s)
    s = FONT.sub("", s)
    s = re.sub(r"\\(lim|limsup|liminf|sup|inf|max|min|log|ln|exp|sin|cos|tan|det|dim|ker|deg|"
               r"gcd|arg|Re|Im|mod|bmod|pmod|arctan|arcsin|arccos|sinh|cosh|tanh|cot|sec|csc|lcm|rank|tr|"
               r"sgn|supp|Hom|id|vol)(?![A-Za-z])", r" \1", s)      # the space keeps \cdot\cot apart
    s = re.sub(r"\\mathcal([A-Za-z])", lambda m: "\x01mathcal" + m.group(1) + "\x02", s)
    def tok(m):
        v = ALIASES.get(m.group(1), m.group(1))
        return "\x01" + v + "\x02" if v[:1].isalpha() else v
    s = re.sub(r"\\([A-Za-z]+)", tok, s)
    s = re.sub(r"\\([{}|_#&%$])", r"\1", s)
    return s


def canon(text: str) -> str:
    text = FENCE.sub("", text)
    # û is u + combining hat; only letters decompose (≠ must stay one symbol)
    text = "".join(unicodedata.normalize("NFD", ch) if ch.isalpha() and not ch.isascii() else ch
                   for ch in text)
    text = text.replace("\\|", "‖").replace("||", "‖")         # \|x\| and ASCII ||x|| are ‖x‖
    text = text.replace("···", "…")                                # ··· is \cdots
    text = text.replace("⟪", "⟨⟨").replace("⟫", "⟩⟩")              # ⟪ is \langle\langle
    text = re.sub(r"\\not\s*\\equiv", "≢", text)
    text = re.sub(r"\\not\s*\\to(?![A-Za-z])", "↛", text)
    text = re.sub(r"\\[dt]?frac\s*\{?1\}?\s*\{?2\}?", "1/2", text)        # ½ is \tfrac12
    text = re.sub(r"\\[()\[\]]", "", text)                        # \( \) \[ \] delimit like $
    text = re.sub(r"(?<=\s)\\ (?=\S)", "\x01setminus\x02", text)   # "ℂ \ C" is ℂ ∖ C; "a\ b" is a space
    text = re.sub(r"\\([_*\[\]#`|<>~])", r"\1", text)          # markdown escapes
    text = text.replace("...", "…")
    text = unicode_tokens(latex_tokens(text))
    text = text.replace("lim\x01sup", "limsup").replace("lim\x01inf", "liminf")
    text = re.sub(r"lim\s*sup", "limsup", text)
    text = re.sub(r"lim\s*inf", "liminf", text)
    text = re.sub(r"\^\{?\s*\*\s*\}?", "*", text)                 # m* is m^*
    text = re.sub(r"\^\{?(?=\x01(?:perp|ast|star|prime|dagger)\x02|')", "", text)   # V⊥ is V^\perp; S′ is S^{\prime}
    text = re.sub(r"[\s${}*`]", "", text)          # spacing, delimiters, grouping, emphasis, code
    text = sqrt_parens(text)                                       # √(C/m(E)) is \\sqrt{C/m(E)}
    text = re.sub(r"L\^(?=[pqr12\x01])", "L", text)              # Lp is L^p
    text = re.sub(r"_(?=\x01[a-z]+\x02)", "", text)                # Gδ is G_\delta
    text = text.replace("^\x01circ\x02", "\x01circ\x02")           # 120° is 120^\circ
    return text


def sqrt_parens(text: str) -> str:
    out, i, key = [], 0, "\x01sqrt\x02("
    while True:
        j = text.find(key, i)
        if j < 0:
            return "".join(out) + text[i:]
        k, depth = j + len(key), 1
        while k < len(text) and depth:
            depth += {"(": 1, ")": -1}.get(text[k], 0)
            k += 1
        if depth:
            return "".join(out) + text[i:]
        out.append(text[i:j] + "\x01sqrt\x02" + text[j + len(key):k - 1])
        i = k


def fences(text: str) -> list[str]:
    return FENCE.findall(text)


def compare(old: str, new: str, label: str) -> bool:
    ok = True
    # A code span may become a formula only if it held mathematics, not a Lean
    # name, a path or a command (all of which the canonical comparison cannot see).
    spans = lambda s: re.findall(r"(?<!`)`([^`\n]+)`(?!`)", FENCE.sub("", s))
    gone = set(spans(old)) - set(spans(new))
    leanish = re.compile(r"[A-Za-z]{2,}\.[A-Za-z]{2,}|[A-Za-z0-9]_[A-Za-z][A-Za-z0-9]{2,}|[A-Za-z]/[A-Za-z]+/|"
                         r"\b(?:lake|by|fun|simp|norm_num|theorem|lemma|def|sorry|Mathlib)\b")
    mathy = re.compile(r"\\[A-Za-z]|[" + "".join(k for k in SYMBOLS if len(k) == 1) + "]")
    for g in sorted(gone):
        if leanish.search(g) and not mathy.search(g) and g == g.strip():
            print(f"{label}: code span `{g[:60]}` is gone but looks like Lean, a path or a command")
            ok = False
    if new.count("`") > old.count("`"):
        print(f"{label}: backticks added ({old.count('`')} -> {new.count('`')}); a formula must not be hidden in code")
        ok = False
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
