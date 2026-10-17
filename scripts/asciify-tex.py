#!/usr/bin/env python3
"""Replace every non-ASCII character in converted proof .tex with LaTeX markup.

pandoc-mathify.lua lifts most mathematics into \\(..\\), but the symbols inside
those spans stay Unicode (\\(‖f‖_p = ∫|f|^p\\)), and symbols in prose it did not
lift stay Unicode in text mode. lualatex sets them through the font and
apm-unicode-math.sty, so the book never complained. Anything that reads the
source as LaTeX does not: pdflatex stops on them, and the futon6 anatomy pass
sees `‖` where it looks for `\\|`.

This pass reads the file the way TeX would, keeping track of math versus text
mode, and writes each character as the command it means:

  in math mode   ∈ -> \\in        ² -> ^{2}        é -> \\text{\\'{e}}
  in text mode   ∈ -> \\ensuremath{\\in}            é -> \\'{e}
  in verbatim    a plain-ASCII stand-in, since commands are not read there

A character with no entry in the tables is an error, not a guess: the file is
left untouched and the character is reported, so the table grows deliberately.

Usage: asciify-tex.py [--write] FILE...
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Mathematics: the command a symbol stands for, valid in math mode.
MATH = {
    # greek
    "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta",
    "ε": r"\varepsilon", "ζ": r"\zeta", "η": r"\eta", "θ": r"\theta",
    "ι": r"\iota", "κ": r"\kappa", "λ": r"\lambda", "μ": r"\mu", "µ": r"\mu",
    "ν": r"\nu", "ξ": r"\xi", "π": r"\pi", "ρ": r"\rho", "σ": r"\sigma",
    "τ": r"\tau", "φ": r"\varphi", "χ": r"\chi", "ψ": r"\psi", "ω": r"\omega",
    "Γ": r"\Gamma", "Δ": r"\Delta", "∆": r"\Delta", "Θ": r"\Theta",
    "Λ": r"\Lambda", "Ξ": r"\Xi", "Π": r"\Pi", "Σ": r"\Sigma", "Φ": r"\Phi",
    "Ψ": r"\Psi", "Ω": r"\Omega",
    # letterlike
    "ℝ": r"\mathbb{R}", "ℂ": r"\mathbb{C}", "ℕ": r"\mathbb{N}",
    "ℤ": r"\mathbb{Z}", "ℚ": r"\mathbb{Q}", "𝔽": r"\mathbb{F}",
    "𝕂": r"\mathbb{K}", "𝓝": r"\mathcal{N}", "ℒ": r"\mathcal{L}",
    "𝒟": r"\mathcal{D}", "𝒮": r"\mathcal{S}", "ℓ": r"\ell",
    "𝟙": r"\mathbf{1}",
    # relations
    "≤": r"\leq", "≥": r"\geq", "≠": r"\neq", "≡": r"\equiv", "≢": r"\not\equiv",
    "≅": r"\cong", "≃": r"\simeq", "≈": r"\approx", "∼": r"\sim", "≪": r"\ll",
    "≲": r"\lesssim", "∈": r"\in", "∉": r"\notin", "∋": r"\ni",
    "⊂": r"\subset", "⊆": r"\subseteq", "⊊": r"\subsetneq", "⊄": r"\not\subset",
    "⊃": r"\supset", "⊇": r"\supseteq", "⊋": r"\supsetneq", "∣": r"\mid",
    "⊥": r"\perp", "⟂": r"\perp",
    # arrows
    "→": r"\to", "↦": r"\mapsto", "⇒": r"\Rightarrow", "⟹": r"\Longrightarrow",
    "⇐": r"\Leftarrow", "⟸": r"\Longleftarrow", "⇔": r"\Leftrightarrow",
    "⟺": r"\Longleftrightarrow", "↔": r"\leftrightarrow", "↑": r"\uparrow",
    "↪": r"\hookrightarrow", "⇏": r"\nRightarrow", "↛": r"\nrightarrow",
    "↠": r"\twoheadrightarrow", "⇀": r"\rightharpoonup",
    "↺": r"\circlearrowleft",
    # operators and other symbols
    "∫": r"\int", "∮": r"\oint", "∭": r"\iiint", "∑": r"\sum", "∏": r"\prod",
    "⋃": r"\bigcup", "⋂": r"\bigcap", "⨆": r"\bigsqcup", "∂": r"\partial",
    "√": r"\sqrt", "·": r"\cdot", "×": r"\times", "÷": r"\div", "±": r"\pm",
    "∘": r"\circ", "∗": r"\ast", "∩": r"\cap", "∪": r"\cup", "⊔": r"\sqcup",
    "⊕": r"\oplus", "⊗": r"\otimes", "⋊": r"\rtimes", "∖": r"\setminus",
    "∧": r"\wedge", "∨": r"\vee", "¬": r"\neg", "∀": r"\forall",
    "∃": r"\exists", "∅": r"\emptyset", "∞": r"\infty", "−": "-",
    "…": r"\ldots", "⋯": r"\cdots", "′": "'", "‖": r"\|", "⟨": r"\langle",
    "⟩": r"\rangle", "⟪": r"\langle\!\langle", "⟫": r"\rangle\!\rangle",
    "‹": r"\langle", "›": r"\rangle", "⌊": r"\lfloor", "⌋": r"\rfloor",
    "⌈": r"\lceil", "⌉": r"\rceil", "△": r"\triangle", "⊤": r"\top",
    "∎": r"\blacksquare", "★": r"\star", "•": r"\bullet", "●": r"\bullet",
    "°": r"^{\circ}", "½": r"\tfrac{1}{2}", "⧸": "/", "✓": r"\checkmark",
    "✔": r"\checkmark", "✗": r"\times", "╲": r"\backslash", "╱": "/",
}

# Unicode super/subscripts, folded run by run into one ^{..} or _{..}.
SUP = dict(zip("⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁿⁱˣᵐᵏᶜᶠᵃˢ", "0123456789+-=()nixmkcfas"))
SUP.update({"ᶿ": r"\theta ", "ᵅ": r"\alpha "})
SUB = dict(zip("₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₙₖₘ", "0123456789+-=()nkm"))

# Combining marks: an accent on whatever came just before.
COMBINING = {"\u0304": r"\bar", "\u0302": r"\hat", "\u0303": r"\tilde",
             "\u0307": r"\dot", "\u0305": r"\bar"}

# Text: characters that are typography, valid in text mode.
TEXT = {
    "é": r"\'{e}", "è": r"\`{e}", "á": r"\'{a}", "à": r"\`{a}", "â": r"\^{a}",
    "ā": r"\={a}", "ó": r"\'{o}", "ô": r"\^{o}", "ö": r'\"{o}', "ü": r'\"{u}',
    "û": r"\^{u}", "ï": r'\"{\i}', "š": r"\v{s}", "Š": r"\v{S}", "č": r"\v{c}",
    "Č": r"\v{C}", "ǧ": r"\v{g}", "ĝ": r"\^{g}", "Ĝ": r"\^{G}", "ŝ": r"\^{s}",
    "—": "---", "–": "--", "‑": "-", "“": "``", "”": "''", "‘": "`", "’": "'",
    "§": r"\S{}", "─": "-", "\u00a0": "~",
    "е": "e",  # Cyrillic ie, a typo for e
}

# Spacing accents written as characters of their own, not combining marks.
SPACING_ACCENT = {"‾": r"\overline{\phantom{x}}", "˙": r"\dot{\phantom{x}}"}

# Inside verbatim nothing is interpreted, so only a plain stand-in will do.
VERBATIM = {"→": "->", "←": "<-", "⇒": "=>", "↦": "|->", "≤": "<=",
            "≥": ">=", "≠": "/=", "─": "-", "│": "|", "×": "x", "·": ".",
            "…": "...", "—": "--", "–": "-", "∈": "in", "‖": "||",
            "−": "-", "∅": "{}",
            # one column each, so ASCII diagrams stay aligned
            "²": "2", "ℝ": "R", "Σ": "S", "↺": "@"}

MATH_ENVS = {"equation", "equation*", "align", "align*", "gather", "gather*",
             "multline", "multline*", "displaymath", "math", "eqnarray",
             "eqnarray*", "flalign", "flalign*", "alignat", "alignat*"}
VERBATIM_ENVS = {"verbatim", "verbatim*", "lstlisting", "minted"}
# A brace group after one of these is text even inside math.
TEXT_IN_MATH = {r"\text", r"\textrm", r"\textit", r"\textbf", r"\textsf",
                r"\texttt", r"\mbox", r"\hbox", r"\textup", r"\textnormal",
                r"\intertext", r"\mMathText", r"\tag", r"\tag*"}
# A brace group after one of these is math even inside text.
MATH_IN_TEXT = {r"\ensuremath"}

TOKEN = re.compile(r"\\[A-Za-z@]+\*?|\\.|\$\$|.", re.S)
ENV = re.compile(r"\{([A-Za-z*]+)\}")


class Unmapped(Exception):
    pass


def math_atom(ch: str) -> str:
    if ch in MATH:
        return MATH[ch]
    if ch in TEXT:
        return r"\text{" + TEXT[ch] + "}"
    if ch in SPACING_ACCENT:
        return SPACING_ACCENT[ch]
    raise Unmapped(ch)


def text_atom(ch: str) -> str:
    if ch in TEXT:
        return TEXT[ch]
    if ch in MATH:
        return r"\ensuremath{" + MATH[ch] + "}"
    if ch in SPACING_ACCENT:
        return r"\ensuremath{" + SPACING_ACCENT[ch] + "}"
    raise Unmapped(ch)


def join(out: list[str], piece: str, nxt: str) -> None:
    """Append a command, keeping it from fusing with a following letter."""
    out.append(piece)
    if re.search(r"\\[A-Za-z]+$", piece) and (nxt.isalpha() and nxt.isascii()):
        out.append(" ")


def asciify(src: str) -> str:
    toks = TOKEN.findall(src)
    out: list[str] = []
    # Mode stack. Each frame is (mode, closer): closer is a delimiter token
    # ("$", "$$", "\\)", "\\]", "end:<env>") or an int brace depth.
    stack: list[tuple[str, object]] = [("text", None)]
    depth = 0
    pending_group: str | None = None  # mode for the next "{" group
    i = 0
    while i < len(toks):
        t = toks[i]
        mode = stack[-1][0]
        nxt = toks[i + 1] if i + 1 < len(toks) else ""

        if mode == "verbatim":
            if t == r"\end" and src_env(toks, i + 1) == stack[-1][1][4:]:
                stack.pop()
                out.append(t)
            elif ord(t[0]) > 127:
                if t not in VERBATIM:
                    raise Unmapped(t)
                out.append(VERBATIM[t])
            else:
                out.append(t)
            i += 1
            continue

        if t == "{":
            depth += 1
            if pending_group:
                stack.append((pending_group, depth))
                pending_group = None
            out.append(t)
        elif t == "}":
            if isinstance(stack[-1][1], int) and stack[-1][1] == depth:
                stack.pop()
            depth -= 1
            out.append(t)
        elif t in ("$", "$$"):
            if stack[-1][1] == t:
                stack.pop()
            elif mode == "text":
                stack.append(("math", t))
            out.append(t)
        elif t in (r"\(", r"\["):
            stack.append(("math", r"\)" if t == r"\(" else r"\]"))
            out.append(t)
        elif t in (r"\)", r"\]"):
            if stack[-1][1] == t:
                stack.pop()
            out.append(t)
        elif t == r"\begin":
            env = src_env(toks, i + 1)
            if env in MATH_ENVS:
                stack.append(("math", "end:" + env))
            elif env in VERBATIM_ENVS:
                # Copy the "{env}" argument verbatim-free first.
                close = toks.index("}", i + 1)
                out.extend(toks[i:close + 1])
                stack.append(("verbatim", "end:" + env))
                i = close + 1
                continue
            out.append(t)
        elif t == r"\end":
            env = src_env(toks, i + 1)
            if stack[-1][1] == "end:" + env:
                stack.pop()
            out.append(t)
        elif t in TEXT_IN_MATH and mode == "math":
            pending_group = "text"
            out.append(t)
        elif t in MATH_IN_TEXT:
            pending_group = "math"
            out.append(t)
        elif t in SUP or t in SUB:
            table, mark = (SUP, "^") if t in SUP else (SUB, "_")
            run = []
            while i < len(toks) and toks[i] in table:
                run.append(table[toks[i]])
                i += 1
            script = mark + "{" + "".join(run).strip() + "}"
            out.append(script if mode == "math" else r"\ensuremath{" + script + "}")
            continue
        elif t in COMBINING:
            base = out.pop() if out and out[-1] not in ("{", "}", " ", "\n") else "{}"
            inner = re.fullmatch(r"\\ensuremath\{(.*)\}", base, re.S)
            base = inner.group(1) if inner else base
            accent = COMBINING[t] + "{" + base + "}"
            out.append(accent if mode == "math" else r"\ensuremath{" + accent + "}")
        elif t == "√":
            # \sqrt takes an argument, so "\ensuremath{\sqrt}x" cannot compile.
            # Take what the radical plainly covers: a run of letters and digits
            # ("√x", "√2n") or a brace group. Anything else ("√(x+1)") gets the
            # bare sign, which sets exactly as the source reads.
            j, arg = i + 1, ""
            if j < len(toks) and toks[j] == "{":
                d = 0
                while j < len(toks):
                    d += toks[j] == "{"
                    d -= toks[j] == "}"
                    arg += toks[j]
                    j += 1
                    if d == 0:
                        break
                arg = arg[1:-1]
            else:
                while j < len(toks) and len(toks[j]) == 1 and toks[j].isascii() and toks[j].isalnum():
                    arg += toks[j]
                    j += 1
            piece = r"\sqrt{" + arg + "}" if arg else r"\surd"
            if mode == "math":
                join(out, piece, toks[j] if j < len(toks) else "")
            else:
                out.append(r"\ensuremath{" + piece + "}")
            i = j
            continue
        elif len(t) == 1 and ord(t) > 127:
            join(out, math_atom(t) if mode == "math" else text_atom(t), nxt)
        else:
            out.append(t)
        i += 1
    return fix_tags("".join(out))


# ---------------------------------------------------------------------------
# Merging fragments into spans.
#
# Symbol by symbol, prose math comes out as
#     \ensuremath{\|}f\ensuremath{\|}\_p \ensuremath{\leq} \(\|f\|_\infty\)
# which compiles but is not mathematics a reader -- or the anatomy pass --
# would recognise. pandoc-mathify leaves similar debris of its own ("\(|f|\)
# \(=\) ..."). merge_math_runs joins each run of math fragments, together with
# the short math-like words between them, into one span:
#     \(\|f\|_p \leq \|f\|_\infty\)
# A run stops at an ordinary word or at sentence punctuation; the lowercase
# article "a" never opens one ("a \sigma-algebra").

GLUE_ATOM = (r"(?:[A-Za-z]"                       # x
             r"|\\_(?:[A-Za-z0-9]|\{[^{}]*\})"        # \_n  (a subscript)
             r"|\\\^\{\}(?:[A-Za-z0-9]|\\\{[^{}]*\\\})"  # \^{}2 (a superscript)
             r"|\([A-Za-z0-9,+\-]{1,6}\)"             # (x), (univ)
             r"|\d+(?:\.\d+)?(?:/\d+)?"               # 2, 0.5, 1/2
             r"|[=+\-<>/|()\[\]]"                     # operators, brackets
             r"|\.\.\."                                  # an ellipsis: 1 + x + ..."
             r"|\\textbar(?:\{\})?"                   # | written as text
             r"|\\textquotesingle(?:\{\})?)")         # a prime written as text
GLUE = re.compile(r"(?:" + GLUE_ATOM + r")+$")


def is_glue(word: str) -> bool:
    """Short math-like words only: two letters side by side ("as", "lim") make
    a word, except as the argument of a function ("m(univ)") or in a
    differential ("dt")."""
    if not GLUE.match(word):
        return False
    # An apostrophe before a letter is English ("'s", "'ll"), not a prime;
    # a run of hyphens is a dash.
    if re.search(r"\\textquotesingle(\{\})?[A-Za-z]", word) or re.fullmatch(r"-{2,}", word):
        return False
    bare = re.sub(r"\\textquotesingle(\{\})?", "'", word)
    bare = re.sub(r"(?<=[A-Za-z'])\([^()]*\)", "", bare)
    bare = re.sub(r"\\textbar(\{\})?|\\_\{[^{}]*\}|\\_.", "", bare)
    bare = re.sub(r"(?<![A-Za-z])d[rstuvwxyz](?![A-Za-z])", "", bare)
    return not re.search(r"[A-Za-z]{2}", bare)


def is_attached_glue(word: str) -> bool:
    """Letters written against a formula with no space between are part of it:
    "1/(2πin²)" reaches here as \\pi, "in", ^{2}, and "in" alone reads as the
    English word, which split the formula at \\pi (a95A07: $1/(2\\pi$in$^{2}$),
    an unclosed bracket LaTeXML renders as CLOSE). Not a hyphenated word
    ("σ-algebra", "ℝ-valued") or an ordinal ending ("n-th")."""
    if re.search(r"-[A-Za-z]{2,}", word) or re.fullmatch(r"-?(?:th|st|nd|rd)", word):
        return False
    return GLUE.match(word) is not None and not re.search(r"[A-Za-z]{4,}", word)


def bracket_balance(text: str) -> int:
    return text.count("(") + text.count("[") - text.count(")") - text.count("]")


def balanced_prefix(run: list[tuple[str, str]]) -> list[tuple[str, str]]:
    """The run, cut before a bracket from the prose that nothing in it matches.

    "$\\bar\\Delta (f$ is univalent, so $f' \\neq 0)$": the "(" opens a remark in
    the sentence, and taking "(f" into the formula left it unclosed (LaTeXML
    renders that as CLOSE) and the remark's ")" stranded in the next formula. A
    bracket inside a formula the source wrote (an M item) is the source's own and
    is left alone.
    """
    while True:
        opens, cut = [], None
        for n, (kind, text) in enumerate(run):
            if kind not in ("M", "G"):
                continue
            for ch in text:
                if ch in "([":
                    opens.append(n)
                elif ch in ")]":
                    if opens:
                        opens.pop()
                    elif kind == "G":
                        cut = n          # closes a bracket opened before the run
                        break
            if cut is not None:
                break
        if cut is None:
            cut = next((n for n in opens if run[n][0] == "G"), None)
        if cut is None:
            return run
        run = run[:cut]
        while run and run[-1][0] in ("S", "C"):
            run.pop()


SENTENCE_PUNCT = re.compile(r"^(.*?)([.,;:!?]+)$")
DISPLAY_OPEN = re.compile(r"\\\[|\$\$|\\begin\{(?:" + "|".join(
    re.escape(e) for e in sorted(MATH_ENVS | VERBATIM_ENVS | {"Highlighting", "Shaded"})) + r")\}")
SKIP_LINE = re.compile(r"\\(?:sub)*section|\\paragraph|\\texorpdfstring|^\s*%")


TEXTLIKE = re.compile(r"\\(?:text|textrm|textit|textbf|mathrm|operatorname|mbox)\{")


def primes(math: str) -> str:
    """Write each run of bare primes as ^{\\prime...}: a lone quote is
    ambiguous between prime and apostrophe, and sets poorly besides. Quotes
    inside \\text{..} and friends are apostrophes and stay."""
    out, i = [], 0
    while i < len(math):
        m = TEXTLIKE.match(math, i)
        if m:
            j = group_end_at(math, m.end() - 1)
            j = j if j > 0 else len(math)
            out.append(math[i:j])
            i = j
            continue
        if math[i] == "\\" and i + 1 < len(math):
            out.append(math[i:i + 2])
            i += 2
            continue
        if math[i] == "'":
            k = i
            while k < len(math) and math[k] == "'":
                k += 1
            sup = "\\prime" * (k - i)
            before = "".join(out)
            # merge with a superscript that follows: f'^{2} -> f^{\prime 2}
            if math.startswith("^{", k):
                e = group_end_at(math, k + 1)
                if e > 0:
                    sup += " " + math[k + 2:e - 1]
                    k = e
            elif re.match(r"\^[A-Za-z0-9]", math[k:]):
                sup += " " + math[k + 1]
                k += 2
            # a superscript just before would make a double superscript
            pad = "{}" if re.search(r"\^(?:\{[^{}]*\}|[A-Za-z0-9])$", before) else ""
            out.append(pad + "^{" + sup + "}")
            i = k
            continue
        out.append(math[i])
        i += 1
    return "".join(out)


def glue_math(word: str) -> str:
    word = word.replace(r"\textbar{}", "|").replace(r"\textbar", "|").replace(r"\_", "_")
    word = word.replace(r"\textquotesingle{}", "'").replace(r"\textquotesingle", "'")
    return re.sub(r"\\\^\{\}\\\{([^{}]*)\\\}|\\\^\{\}(.)", lambda m: "^{" + (m.group(1) or m.group(2)) + "}", word)


def line_segments(line: str) -> list[tuple[str, str]] | None:
    """Split a line into ("M", math) and ("T", text) segments, or None if a
    math span does not close on this line."""
    segs, i, buf = [], 0, []
    while i < len(line):
        if line.startswith(r"\(", i):
            j = line.find(r"\)", i + 2)
            if j < 0:
                return None
            kind, inner, i = "M", line[i + 2:j], j + 2
        elif line.startswith(r"\ensuremath{", i):
            j = group_end_at(line, i + len(r"\ensuremath"))
            if j < 0:
                return None
            kind, inner, i = "M", line[i + len(r"\ensuremath{"):j - 1], j
        elif line[i] == "\\" and i + 1 < len(line):
            buf.append(line[i:i + 2])
            i += 2
            continue
        elif line[i] == "$":
            j = line.find("$", i + 1)
            if j < 0 or line.startswith("$$", i):
                return None
            kind, inner, i = "M", line[i + 1:j], j + 1
        else:
            buf.append(line[i])
            i += 1
            continue
        if buf:
            segs.append(("T", "".join(buf)))
            buf = []
        segs.append((kind, inner))
    if buf:
        segs.append(("T", "".join(buf)))
    return segs


def group_end_at(s: str, i: int) -> int:
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        depth += c == "{"
        depth -= c == "}"
        j += 1
        if depth == 0:
            return j
    return -1


def strip_ensuremath(math: str) -> str:
    while True:
        i = math.find(r"\ensuremath{")
        if i < 0:
            return math
        j = group_end_at(math, i + len(r"\ensuremath"))
        if j < 0:
            return math
        math = math[:i] + math[i + len(r"\ensuremath{"):j - 1] + math[j:]


def anchor(kind: str, text: str) -> bool:
    """A run becomes a math span if it holds a math fragment, or a prime:
    "f\\textquotesingle(t)" is f'(t) even with no span beside it."""
    return kind == "M" or (kind == "G" and "\\textquotesingle" in text)


def merge_line(line: str) -> str:
    segs = line_segments(line)
    if segs is None or sum(k == "M" for k, _ in segs) == 0:
        return line
    # items: (kind, text) with kind M, G (glue word), S (space), W (other)
    items: list[tuple[str, str]] = []
    for n, (kind, text) in enumerate(segs):
        if kind == "M":
            # \ensuremath inside a math span is a no-op the converters leave
            # behind (fold-unicode-scripts writes \ensuremath{_{0}} in math too).
            items.append(("M", strip_ensuremath(text)))
            continue
        # "\textquotesingle s" is "'s" to TeX (a control word eats the space
        # after it); write it that way so the apostrophe test below sees it.
        text = re.sub(r"\\textquotesingle\s+(?=[A-Za-z])", r"\\textquotesingle{}", text)
        pieces = re.findall(r"\s+|\S+", text)
        for at, piece in enumerate(pieces):
            # touching a formula on either side, with no space between
            attached = ((at == 0 and n > 0 and segs[n - 1][0] == "M")
                        or (at == len(pieces) - 1 and n + 1 < len(segs) and segs[n + 1][0] == "M"))
            if piece.isspace():
                items.append(("S", piece))
                continue
            m = SENTENCE_PUNCT.match(piece)
            core, punct = (m.group(1), m.group(2)) if m else (piece, "")
            # Three letters at least: "(kx)", "(ab)", "(iy)" are products.
            wordarg = re.match(r"\(([A-Za-z]{3,12})\)", core)
            if (wordarg and items and items[-1][0] == "M"
                    and (core[wordarg.end():] == "" or is_glue(core[wordarg.end():]))):
                # mu(univ)=1: a function applied to a word, set as \text
                items.append(("G", "(\\text{" + wordarg.group(1) + "})"
                              + core[wordarg.end():]))
                if punct:
                    items.append(("C" if punct == "," else "W", punct))
            elif core and (is_glue(core) or (attached and is_attached_glue(core))):
                items.append(("G", core))
                if punct:
                    items.append(("C" if punct == "," else "W", punct))
            elif piece == ",":
                items.append(("C", ","))
            else:
                items.append(("W", piece))
    # A glued word splits at its brackets, so a cut for balance falls at the
    # bracket ("3/2)" keeps 3/2 in the formula and leaves the ")"), not at the word.
    split = []
    for kind, text in items:
        if kind == "G" and "\\" not in text:
            split.extend(("G", part) for part in re.findall(r"[()\[\]]|[^()\[\]]+", text))
        else:
            split.append((kind, text))
    items = split
    out, i = [], 0
    while i < len(items):
        kind, text = items[i]
        if kind not in ("M", "G") or (kind == "G" and text == "a"):
            out.append(text if kind != "M" else r"\(" + primes(text) + r"\)")
            i += 1
            continue
        # Extend a candidate run over M, G and the spaces between them, and over
        # a comma while a bracket the run opened is still open: "(a_i, b_i)" is
        # one tuple, but "f, g and h" is a list in prose.
        j, last = i, i
        while j < len(items) and items[j][0] in ("M", "G", "S", "C"):
            if items[j][0] == "C" and bracket_balance(
                    "".join(t for k, t in items[i:j] if k in ("M", "G"))) <= 0:
                break
            if items[j][0] not in ("S", "C"):
                last = j
            j += 1
        run = items[i:last + 1]
        # the article "a" does not end a span either
        while len(run) > 1 and run[-1][0] in ("G", "S") and (run[-1][0] == "S" or run[-1][1] == "a"):
            run.pop()
        # A bracket glued on at either end must be closed inside the span, or
        # the span would open "(" in math and close ")" in text. The count is over
        # the whole run: "$1/(2\\pi$in$^{2}$)" opens its bracket inside a formula.
        while run and run[0][0] in ("G", "S") and (run[0][0] == "S" or (
                re.fullmatch(r"[(\[]+", run[0][1]) and bracket_balance(
                    "".join(t for k, t in run if k != "S")) > 0)):
            out.append(run.pop(0)[1])
            i += 1
        while run and run[-1][0] in ("G", "S") and (run[-1][0] == "S" or (
                re.fullmatch(r"[)\]]+", run[-1][1]) and bracket_balance(
                    "".join(t for k, t in run if k != "S")) < 0)):
            run.pop()
        run = balanced_prefix(run)
        if not run:
            out.append(text)
            i += 1
            continue
        if not any(anchor(k, t) for k, t in run):
            out.append(text)
            i += 1
            continue
        body = ""
        for k, t in run:
            piece = " " if k == "S" else ("," if k == "C" else (glue_math(t) if k == "G" else t))
            # "\varphi" + "A" must not fuse into the undefined "\varphiA".
            if re.search(r"\\[A-Za-z]+$", body) and re.match(r"[A-Za-z]", piece):
                body += " "
            body += piece
        out.append(r"\(" + primes(body.strip()) + r"\)")
        i += len(run)
    return "".join(out)


def merge_math_runs(src: str) -> str:
    lines = src.split("\n")
    closer = None
    for n, line in enumerate(lines):
        if closer:
            if re.search(closer, line):
                closer = None
            continue
        m = DISPLAY_OPEN.search(line)
        if m:
            tok = m.group(0)
            closer = (re.escape(r"\]") if tok == r"\[" else re.escape("$$") if tok == "$$"
                      else re.escape(tok.replace(r"\begin", r"\end")))
            # a display that opens and closes on one line ends here
            if re.search(closer, line[m.end():]):
                closer = None
            continue
        if SKIP_LINE.search(line):
            continue
        lines[n] = merge_line(line)
    return "\n".join(lines)


# Math-only symbols the converter writes as equation tags. A tag is set in
# text mode: lualatex lets "\tag{\ast}" through, pdflatex stops on it.
TAG_SYMBOL = re.compile(r"\\tag(\*?)\{(\\(?:ast|dagger|ddagger|star|bullet|circ|sharp|flat|natural))\}")


def fix_tags(src: str) -> str:
    return TAG_SYMBOL.sub(r"\\tag\1{\\ensuremath{\2}}", src)


def src_env(toks: list[str], j: int) -> str:
    """The environment name in the "{name}" tokens starting at toks[j]."""
    m = ENV.match("".join(toks[j:j + 40]))
    return m.group(1) if m else ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()
    changed = chars = 0
    failed: dict[str, list[str]] = {}
    for f in args.files:
        p = Path(f)
        src = p.read_text(encoding="utf-8")
        n = sum(1 for c in src if ord(c) > 127)
        try:
            dst = merge_math_runs(asciify(src))
        except Unmapped as e:
            failed.setdefault(str(e), []).append(p.name)
            continue
        left = sorted({c for c in dst if ord(c) > 127})
        if left:
            failed.setdefault("".join(left), []).append(p.name)
            continue
        if dst == src:
            continue
        changed += 1
        chars += n
        if args.write:
            p.write_text(dst, encoding="utf-8")
    print(f"Asciified {chars} character(s) in {changed} file(s)")
    for ch, names in sorted(failed.items()):
        print(f"  unmapped {ch!r} (U+{ord(ch[0]):04X}) in {len(names)} file(s): "
              f"{' '.join(names[:5])}", file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
