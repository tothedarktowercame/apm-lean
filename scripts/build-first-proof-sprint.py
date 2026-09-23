#!/usr/bin/env python3
"""Assemble converted APM informal proofs into one First Proof Sprint document.

Reads the .tex produced by informal-proofs-to-tex.sh, pairs each with its
problem statement, and writes a master document ready for lualatex.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CODE_ROOT = REPO_ROOT.parent

# Base letter + combining accent is text-mode nonsense in LaTeX; fold it into a
# real math accent so \hat{f} sets as an accent rather than a dropped glyph.
COMBINING = {"\u0302": "hat", "\u0303": "tilde", "\u0304": "bar", "\u0307": "dot"}


def fold_combining(text: str) -> tuple[str, int]:
    out, n, i = [], 0, 0
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if nxt in COMBINING and (ch.isalpha() and ch.isascii()):
            out.append(rf"\ensuremath{{\{COMBINING[nxt]}{{{ch}}}}}")
            i += 2
            n += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out), n


# A proof's headings come back at whatever level its markdown asked for. Most
# files open with "# " and so with \section; six open with "## " and so a level
# down; four carry no heading at all. Retarget each file onto the ladder the
# master document uses, so every proof's title lands at the top of that ladder
# whatever its source looked like. This is not cosmetic: --splitat=section cuts
# a page at each top-level heading, so a title one level too deep is swallowed
# by the preceding proof's page and a file with two of them is torn in half.
#
# SRC_LEVELS is what pandoc emits (it has no \chapter without
# --top-level-division); the other two are the ladders the two targets want.
SRC_LEVELS = ["section", "subsection", "subsubsection", "paragraph"]
ARTICLE_LEVELS = ["section", "subsection", "subsubsection", "paragraph"]
BOOK_LEVELS = ["chapter", "section", "subsection", "subsubsection"]

HEADING_RE = re.compile(r"\\(subsubsection|subsection|section|paragraph)(\*?)\{")


def wanted_lean(pid: str, mode: str) -> bool:
    """Should this problem's Lean proof be included?

    "complete" reads lean.sorry_count_total from status.json rather than
    grepping the source: 51 of the files carry the word `sorry` only inside a
    comment or a docstring, and 7 have no audited count at all. The field was
    written by an elaboration audit, so it is the one number that means what it
    says."""
    if mode == "all":
        return True
    status = REPO_ROOT / "problems" / pid / "status.json"
    if not status.is_file():
        return False
    try:
        return json.loads(status.read_text()).get("lean", {}).get(
            "sorry_count_total") == 0
    except (ValueError, OSError):
        return False


def retarget_headings(body: str, levels: list[str]) -> tuple[str, bool]:
    """Shift a proof's headings so its shallowest sits at levels[0].

    Returns the rewritten body and whether any heading was found at all."""
    depths = [SRC_LEVELS.index(m.group(1)) for m in HEADING_RE.finditer(body)]
    if not depths:
        return body, False
    lo = min(depths)

    def repl(m: re.Match) -> str:
        i = min(SRC_LEVELS.index(m.group(1)) - lo, len(levels) - 1)
        return "\\" + levels[i] + m.group(2) + "{"

    return HEADING_RE.sub(repl, body), True


def titles_itself(body: str, pid: str, macro: str) -> bool:
    """Does the proof's own first heading say which problem this is?

    481 of the 501 open "# APM a94J02: ...". The rest open with a generic
    "Informal solution", or with "## 1. Informal proof", or with no heading at
    all -- page titles that tell a reader nothing about which problem they are
    reading."""
    i = body.find(macro)
    if i < 0:
        return False
    end = heading_end(body, macro)
    return pid.lower() in body[i:end].lower() if end else False


def retitle(body: str, pid: str, levels: list[str]) -> tuple[str, bool]:
    """Guarantee exactly one levels[0] heading, and that it names the problem.

    --splitat=section gives one page per levels[0] heading, so a proof with
    none is swallowed by its neighbour and a proof with two is torn in half."""
    body, had = retarget_headings(body, levels)
    synthesized = False
    if not (had and titles_itself(body, pid, "\\" + levels[0] + "{")):
        # Demote whatever structure the file has and give it a real title.
        body, _ = retarget_headings(body, levels[1:])
        body = (f"\\{levels[0]}{{apm-{pid}}}\\label{{apm-{pid.lower()}}}\n\n"
                + body.lstrip("\n"))
        synthesized = True

    # A title wrapped across two markdown lines, both starting with "#", comes
    # back as two headings; demote every one after the first.
    top_re = re.compile(re.escape("\\" + levels[0]) + r"(\*?)\{")
    seen = 0

    def demote(m: re.Match) -> str:
        nonlocal seen
        seen += 1
        return m.group(0) if seen == 1 else "\\" + levels[1] + m.group(1) + "{"

    return top_re.sub(demote, body), synthesized


def heading_end(body: str, macro: str) -> int | None:
    """Index just past the title heading, counting braces rather than matching
    a regex: pandoc wraps titles in \\texorpdfstring{..}{..}, so a non-greedy
    \\chapter\\{.*?\\} stops at the first inner brace and splits the macro."""
    i = body.find(macro)
    if i < 0:
        return None
    j = i + len(macro)
    depth = 1
    while j < len(body) and depth:
        c = body[j]
        if c == "\\":
            j += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        j += 1
    # Absorb a trailing \label{..} and pandoc's closing hypertarget brace.
    m = re.compile(r"\s*\\label\{[^}]*\}\}?").match(body, j)
    return m.end() if m else j


LATEXML_PREAMBLE = r"""\documentclass[11pt]{article}
% mathtools supplies psmallmatrix and the extensible arrows the proofs use;
% LaTeXML has a binding for it, so it costs nothing here.
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{longtable,booktabs}
\usepackage{enumitem}
\usepackage{hyperref}
% alltt is how a highlighted listing survives to HTML: LaTeXML's binding emits
% <ltx:verbatim> with newlines and leading spaces preserved, while leaving \{}
% alive so pandoc's token macros still fire. That is exactly what fancyvrb's
% commandchars=\\\{\} buys in the PDF, and LaTeXML has no binding for fancyvrb.
\usepackage{alltt}
\usepackage{xcolor}

% LaTeXML reads Unicode natively, so apm-unicode-math.sty is not loaded here --
% its \newunicodechar mappings exist only because Latin Modern lacks the glyphs
% in PDF output. Nor are the page-layout packages (geometry, fancyhdr,
% microtype, tcolorbox): they describe pages, and this target has none.

% A gloss from render-lean-proofs.py. Here it is a margin note: LaTeXML renders
% \marginpar as a note and tuftify lifts it into the Tufte margin, which is the
% column these are written for.
\newcommand{\apmgloss}[1]{\marginpar{\small #1}}
% A link from a name in the informal proof to the Lean proof that uses it
% (annotate-lean-links.py). A footnote rather than a \marginpar because tuftify
% renders a footnote as a NUMBERED Tufte sidenote, and the note is keyed to one
% word, so the reader has to be able to see which.
\newcommand{\apmlink}[1]{\footnote{#1}}

% Syntax-class markup from pandoc-mathify.lua, flattened to identity.
\newcommand{\mNumber}[1]{#1}
\newcommand{\mConstant}[1]{#1}
\newcommand{\mExponent}[1]{#1}
\newcommand{\mSubscript}[1]{#1}
\newcommand{\mGreek}[1]{#1}
\newcommand{\mOperator}[1]{#1}
\newcommand{\mBridgeOperator}[1]{#1}
\newcommand{\mRelation}[1]{#1}
\newcommand{\mCompare}[1]{#1}
\newcommand{\mLargeOperator}[1]{#1}
\newcommand{\mArrow}[1]{#1}
\newcommand{\mDelimiter}[1]{#1}
\newcommand{\mFunction}[1]{#1}
\newcommand{\mMathText}[1]{#1}
\newcommand{\mMathItalic}[1]{#1}
\newcommand{\mVariable}[1]{#1}
\newcommand{\mQuantifier}[1]{#1}
\newcommand{\mBin}[1]{\mathbin{#1}}
\newcommand{\mRel}[1]{\mathrel{#1}}
\newcommand{\mDelim}[1]{#1}
\newcommand{\mPow}[2]{#1^{#2}}
\newcommand{\mIdx}[2]{#1_{#2}}
\newcommand{\mTensor}[3]{#1_{#2}^{#3}}
\newcommand{\mOpName}[1]{\operatorname{#1}}
\newcommand{\mDualStar}{\ast}
\newcommand{\EulerE}{e}
\providecommand{\Integral}{\int}
\providecommand{\integral}{\int}
\providecommand{\mathup}[1]{\mathrm{#1}}

% pandoc body output.
\providecommand{\tightlist}{}
\newenvironment{Shaded}{}{}
% Highlighting takes an optional argument from pandoc. Do not try to wrap
% verbatim here: verbatim fixes catcodes when it is *defined*, so nesting it
% inside another environment ends the document early. alltt has no such
% problem, and unlike the \ttfamily paragraph this replaces, it keeps the line
% breaks and the indentation -- without which a Lean proof arrives in HTML as
% one run-on line of typewriter text.
\newenvironment{Highlighting}[1][]{\begin{alltt}}{\end{alltt}}
\providecommand{\AlertTok}[1]{\textcolor[rgb]{1.00,0.00,0.00}{\textbf{\texttt{#1}}}}
\providecommand{\AnnotationTok}[1]{\textcolor[rgb]{0.38,0.63,0.69}{\textbf{\textit{\texttt{#1}}}}}
\providecommand{\AttributeTok}[1]{\textcolor[rgb]{0.49,0.56,0.16}{\texttt{#1}}}
\providecommand{\BaseNTok}[1]{\textcolor[rgb]{0.25,0.63,0.44}{\texttt{#1}}}
\providecommand{\BuiltInTok}[1]{\textcolor[rgb]{0.00,0.50,0.00}{\texttt{#1}}}
\providecommand{\CharTok}[1]{\textcolor[rgb]{0.25,0.44,0.63}{\texttt{#1}}}
\providecommand{\CommentTok}[1]{\textcolor[rgb]{0.38,0.63,0.69}{\textit{\texttt{#1}}}}
\providecommand{\CommentVarTok}[1]{\textcolor[rgb]{0.38,0.63,0.69}{\textbf{\textit{\texttt{#1}}}}}
\providecommand{\ConstantTok}[1]{\textcolor[rgb]{0.53,0.00,0.00}{\texttt{#1}}}
\providecommand{\ControlFlowTok}[1]{\textcolor[rgb]{0.00,0.44,0.13}{\textbf{\texttt{#1}}}}
\providecommand{\DataTypeTok}[1]{\textcolor[rgb]{0.56,0.13,0.00}{\texttt{#1}}}
\providecommand{\DecValTok}[1]{\textcolor[rgb]{0.25,0.63,0.44}{\texttt{#1}}}
\providecommand{\DocumentationTok}[1]{\textcolor[rgb]{0.73,0.13,0.13}{\textit{\texttt{#1}}}}
\providecommand{\ErrorTok}[1]{\textcolor[rgb]{1.00,0.00,0.00}{\textbf{\texttt{#1}}}}
\providecommand{\ExtensionTok}[1]{#1}
\providecommand{\FloatTok}[1]{\textcolor[rgb]{0.25,0.63,0.44}{\texttt{#1}}}
\providecommand{\FunctionTok}[1]{\textcolor[rgb]{0.02,0.16,0.49}{\texttt{#1}}}
\providecommand{\ImportTok}[1]{\textcolor[rgb]{0.00,0.50,0.00}{\textbf{\texttt{#1}}}}
\providecommand{\InformationTok}[1]{\textcolor[rgb]{0.38,0.63,0.69}{\textbf{\textit{\texttt{#1}}}}}
\providecommand{\KeywordTok}[1]{\textcolor[rgb]{0.00,0.44,0.13}{\textbf{\texttt{#1}}}}
\providecommand{\NormalTok}[1]{#1}
\providecommand{\OperatorTok}[1]{\textcolor[rgb]{0.40,0.40,0.40}{\texttt{#1}}}
\providecommand{\OtherTok}[1]{\textcolor[rgb]{0.00,0.44,0.13}{\texttt{#1}}}
\providecommand{\PreprocessorTok}[1]{\textcolor[rgb]{0.74,0.48,0.00}{\texttt{#1}}}
\providecommand{\RegionMarkerTok}[1]{#1}
\providecommand{\SpecialCharTok}[1]{\textcolor[rgb]{0.25,0.44,0.63}{\texttt{#1}}}
\providecommand{\SpecialStringTok}[1]{\textcolor[rgb]{0.73,0.40,0.53}{\texttt{#1}}}
\providecommand{\StringTok}[1]{\textcolor[rgb]{0.25,0.44,0.63}{\texttt{#1}}}
\providecommand{\VariableTok}[1]{\textcolor[rgb]{0.10,0.09,0.49}{\texttt{#1}}}
\providecommand{\VerbatimStringTok}[1]{\textcolor[rgb]{0.25,0.44,0.63}{\texttt{#1}}}
\providecommand{\WarningTok}[1]{\textcolor[rgb]{0.38,0.63,0.69}{\textbf{\textit{\texttt{#1}}}}}


% APM problem-statement macros and list flavours.
\newenvironment{alist}{\begin{enumerate}[label=(\alph*)]}{\end{enumerate}}
\newenvironment{rlist}{\begin{enumerate}[label=(\roman*)]}{\end{enumerate}}
\newenvironment{123list}{\begin{enumerate}[label=(\arabic*)]}{\end{enumerate}}
\newenvironment{Rlist}{\begin{enumerate}[label=(\Roman*)]}{\end{enumerate}}
\newcommand{\R}{\mathbb{R}}
\newcommand{\Rn}{\mathbb{R}^n}
\newcommand{\Rm}{\mathbb{R}^m}
\newcommand{\Rtw}{\mathbb{R}^2}
\newcommand{\Rth}{\mathbb{R}^3}
\newcommand{\Rfo}{\mathbb{R}^4}
\newcommand{\RP}{\mathbb{R}\mathrm{P}}
\newcommand{\CP}{\mathbb{C}\mathrm{P}}
\newcommand{\C}{\mathbb{C}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Q}{\mathbb{Q}}
\newcommand{\N}{\mathbb{N}}
\providecommand{\T}{\mathbb{T}}
\newcommand{\Son}{S^1}
\newcommand{\Stw}{S^2}
\newcommand{\Sth}{S^3}
\newcommand{\Sfo}{S^4}
\newcommand{\Sfi}{S^5}
\newcommand{\Sn}{S^n}
\newcommand{\Ttw}{T^2}
\newcommand{\ie}{i.e.}
\newcommand{\Ie}{I.e.}
\newcommand{\pipe}{\mid}
\newcommand{\soln}[1]{}
\providecommand{\defn}[1]{#1}
\providecommand{\id}{\mathrm{id}}
\newcommand{\dbyd}[1]{\frac{\mathrm{d}}{\mathrm{d}#1}}
\newcommand{\dbydk}[2]{\frac{\mathrm{d}^{#2}}{\mathrm{d}#1^{#2}}}
\newcommand{\pbyp}[1]{\frac{\partial}{\partial #1}}
\newcommand{\pbypk}[2]{\frac{\partial^{#2}}{\partial #1^{#2}}}
\newcommand{\ddk}[3]{\frac{\mathrm{d}^{#3} #1}{\mathrm{d} #2^{#3}}}
\DeclareMathOperator{\im}{im}
\DeclareMathOperator{\vol}{vol}
\DeclareMathOperator*{\esssup}{ess\,sup}
\DeclareMathOperator*{\essinf}{ess\,inf}
\providecommand{\fint}{\int}
\providecommand{\longhookrightarrow}{\hookrightarrow}

\newenvironment{problemstatement}
  {\par\medskip\noindent\textbf{Problem.}\enspace\ignorespaces}
  {\par\medskip}

\title{\textbf{A First Proof Sprint}\\[0.4em]
  \large APM Informal Proofs, Translated to \LaTeX}
\author{Joseph Corneli and Claude}
\date{\today}

\begin{document}
\maketitle

\section*{About this collection}

This is the complete set of @TOTAL@ informal proofs in the APM Lean collection
(\texttt{problems/<id>/informal-solution.md}), translated to \LaTeX{} by the
First Proof Sprint recipe and rendered here by LaTeXML.

\tableofcontents

"""


PREAMBLE = r"""\documentclass[11pt,oneside]{book}
\usepackage[margin=1.1in]{geometry}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage[dvipsnames]{xcolor}
% The Lean listings are written in Lean's Unicode: 𝕜, ⊢, ⨅, x⁻¹, aₐ, ⦃e⦄.
% Latin Modern Mono has none of it -- 9,460 missing characters across the
% corpus, every one of them inside a listing. JuliaMono was built for exactly
% this (it is what the Lean community uses) and covers all 74 of the code
% points involved; it ships with TeX Live, so fontspec finds it by name.
% MatchLowercase keeps it from towering over the body face.
\usepackage{fontspec}
\setmonofont{JuliaMono}[Scale=MatchLowercase]
\usepackage{enumitem}
\usepackage{longtable,booktabs}
\usepackage{microtype}
\usepackage{xurl}
\usepackage{hyperref}
\hypersetup{colorlinks=true,linkcolor=blue!50!black,urlcolor=blue!60!black,
  pdftitle={A First Proof Sprint: APM Informal Proofs in LaTeX},
  pdfauthor={Joseph Corneli and Claude}}

% Macros pandoc's own template would define; we take only its body output.
\usepackage{apm-pandoc-compat}

% A gloss from render-lean-proofs.py. The book layout has no margin column, and
% 2,891 floating \marginpars would fight the page on every spread, so here the
% note is set inline above the listing it describes.
\newcommand{\apmgloss}[1]{\par{\footnotesize\itshape #1\par}\nobreak}
\newcommand{\apmlink}[1]{\footnote{#1}}
% Syntax-class markup emitted by pandoc-mathify.lua (colours off by default).
\usepackage{math-proofread-style}
% math-proofread-style defines the \m... syntax-class macros to colour their
% argument unconditionally, which is right for proofreading and wrong for a
% reading copy (every integer comes out red). Flatten them to identity unless
% APMPROOFREADCOLOURS is set.
\makeatletter
\@ifundefined{APMProofreadColours}{%
  \renewcommand{\mNumber}[1]{#1}%
  \renewcommand{\mConstant}[1]{#1}%
  \renewcommand{\mExponent}[1]{#1}%
  \renewcommand{\mSubscript}[1]{#1}%
  \renewcommand{\mGreek}[1]{#1}%
  \renewcommand{\mOperator}[1]{#1}%
  \renewcommand{\mBridgeOperator}[1]{#1}%
  \renewcommand{\mRelation}[1]{#1}%
  \renewcommand{\mCompare}[1]{#1}%
  \renewcommand{\mLargeOperator}[1]{#1}%
  \renewcommand{\mArrow}[1]{#1}%
  \renewcommand{\mDelimiter}[1]{#1}%
  \renewcommand{\mFunction}[1]{#1}%
  \renewcommand{\mMathText}[1]{#1}%
  \renewcommand{\mMathItalic}[1]{#1}%
  \renewcommand{\mOpName}[1]{\mathop{\mathrm{#1}}\nolimits}%
}{}
\makeatother

% Residual Unicode math left in text mode by the converter.
\usepackage{apm-unicode-math}

% APM problem-statement macros (from apm/project-cheatsheet.py).
\newcommand{\R}{\mathbb{R}}
\newcommand{\Rn}{\mathbb{R}^n}
\newcommand{\Rtw}{\mathbb{R}^2}
\newcommand{\RP}{\mathbb{R}\mathrm{P}}
\newcommand{\C}{\mathbb{C}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Son}{S^1}
\newcommand{\Stw}{S^2}
\newcommand{\Sth}{S^3}
\newcommand{\Ttw}{T^2}
% Further APM shorthands, read off from their use in the problem statements:
% \Sfi appears as $\Sfi\subset\C^3\cong\R^6$, so it is the 5-sphere.
\newcommand{\CP}{\mathbb{C}\mathrm{P}}
\newcommand{\Sn}{S^n}
\newcommand{\Sfo}{S^4}
\newcommand{\Sfi}{S^5}
\newcommand{\Rfo}{\mathbb{R}^4}
\newcommand{\pbyp}[1]{\frac{\partial}{\partial #1}}
\newcommand{\pbypk}[2]{\frac{\partial^{#2}}{\partial #1^{#2}}}
\newcommand{\ddk}[3]{\frac{\mathrm{d}^{#3} #1}{\mathrm{d} #2^{#3}}}
\DeclareMathOperator{\im}{im}
\DeclareMathOperator{\vol}{vol}
\providecommand{\longhookrightarrow}{\lhook\joinrel\relbar\joinrel\rightarrow}
\newcommand{\Rm}{\mathbb{R}^m}
\newcommand{\dbyd}[1]{\frac{\mathrm{d}}{\mathrm{d}#1}}
\newcommand{\dbydk}[2]{\frac{\mathrm{d}^{#2}}{\mathrm{d}#1^{#2}}}
\providecommand{\id}{\mathrm{id}}
% Average integral; esint is not assumed, so strike the integral sign directly.
\providecommand{\fint}{\rlap{\kern.09em\rule[.62ex]{.5em}{.05ex}}\int}
\providecommand{\defn}[1]{#1}
\newcommand{\Rth}{\mathbb{R}^3}
\newcommand{\Ie}{I.e.}
\newcommand{\Q}{\mathbb{Q}}
\newcommand{\N}{\mathbb{N}}
\DeclareMathOperator*{\esssup}{ess\,sup}
\DeclareMathOperator*{\essinf}{ess\,inf}
\newcommand{\ie}{i.e.}
\newcommand{\pipe}{\mid}
\newcommand{\soln}[1]{}

\newenvironment{problemstatement}
  {\par\medskip\noindent\begin{minipage}{\linewidth}%
   \color{black!75}\small\textbf{Problem.}\enspace\ignorespaces}
  {\end{minipage}\par\medskip}

% Chapter titles are full sentences and overflow the running head, so each
% chapter sets its own short mark (the problem id) instead.
\usepackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small\itshape\nouppercase{\leftmark}}
\fancyhead[R]{\small\thepage}
\renewcommand{\headrulewidth}{0.4pt}
\fancypagestyle{plain}{\fancyhf{}\fancyfoot[C]{\small\thepage}\renewcommand{\headrulewidth}{0pt}}

\setlength{\parskip}{0.35em}
\setlength{\parindent}{0pt}
\setcounter{tocdepth}{1}

\title{\textbf{A First Proof Sprint}\\[0.4em]
  \large APM Informal Proofs, Translated to \LaTeX}
\author{Joseph Corneli and Claude}
\date{\today}

\begin{document}
\maketitle

\chapter*{About this sample}
\addcontentsline{toc}{chapter}{About this sample}

This is a @NPROOFS@-proof sample drawn from the @TOTAL@ informal proofs in the APM
Lean collection (\texttt{problems/<id>/informal-solution.md}). Each proof is
translated by the First Proof Sprint recipe --- \texttt{normalize-math-prose.py},
then \texttt{pandoc} through the \texttt{pandoc-mathify.lua} filter --- with the
source markdown never mutated.

The sample deliberately spans all three markdown shapes present in the
collection and all four problem families, including the two hardest cases: a
proof written with no \texttt{\$}-delimited math at all, and the proof carrying
the heaviest display-math load.

\tableofcontents

"""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("id_list")
    ap.add_argument("tex_dir")
    ap.add_argument("out")
    ap.add_argument("--total", type=int, default=491)
    ap.add_argument("--latexml", action="store_true",
                    help="emit a preamble LaTeXML can digest (no page layout, "
                         "no \\newunicodechar, proofread macros flattened)")
    ap.add_argument("--lean", choices=("all", "complete", "none"), default="all",
                    help="which Lean proofs to append below the informal one: "
                         "all that exist (default), only those the sorry audit "
                         "in status.json records as sorry-free, or none")
    args = ap.parse_args()

    ids = [x.strip() for x in Path(args.id_list).read_text().split() if x.strip()]
    tex_dir = Path(args.tex_dir)
    chosen = LATEXML_PREAMBLE if args.latexml else PREAMBLE
    parts = [chosen.replace("@NPROOFS@", str(len(ids)))
                   .replace("@TOTAL@", str(args.total))]
    folded_total = 0
    titled = 0
    lean_included = 0

    for pid in ids:
        body_path = tex_dir / f"apm-{pid}.tex"
        if not body_path.is_file():
            print(f"missing converted proof: {body_path}", file=sys.stderr)
            return 1
        body, folded = fold_combining(body_path.read_text())
        folded_total += folded

        levels = BOOK_LEVELS if not args.latexml else ARTICLE_LEVELS
        body, synthesized = retitle(body, pid, levels)
        titled += synthesized

        stmt_path = REPO_ROOT / "problems" / pid / "problem.tex"
        stmt = stmt_path.read_text().strip() if stmt_path.is_file() else ""

        # Insert the problem statement directly under the chapter heading, so a
        # reader meets the question before the answer. pandoc wraps the heading
        # as \hypertarget{..}{%\n\\chapter{..}\\label{..}}; split after that block.
        if stmt:
            block = "\n\\begin{problemstatement}\n" + stmt + "\n\\end{problemstatement}\n"
            cut = heading_end(body, "\\" + levels[0] + "{")
            if cut is not None:
                body = body[:cut] + "\n" + block + body[cut:]
            else:
                body = block + body

        # The Lean proof goes below the informal argument, one level down, so
        # --splitat=section keeps the two on the same page: a reader meets the
        # question, then the prose answer, then the machine-checked one.
        lean_path = tex_dir / "lean" / f"apm-{pid}.tex"
        if args.lean != "none" and lean_path.is_file() and wanted_lean(pid, args.lean):
            body = (body.rstrip("\n") + "\n\n\\" + levels[1]
                    + "{Lean proof}\n\n" + lean_path.read_text().rstrip("\n") + "\n")
            lean_included += 1

        parts.append(f"\n%% ==== {pid} ====\n")
        parts.append(body)
        if not args.latexml:
            parts.append(f"\n\\chaptermark{{APM {pid}}}\n")

    parts.append("\n\\end{document}\n")
    Path(args.out).write_text("".join(parts))
    print(f"Wrote {args.out} ({len(ids)} proofs, {folded_total} combining "
          f"accents folded, {titled} proofs given a title, "
          f"{lean_included} Lean proofs appended)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
