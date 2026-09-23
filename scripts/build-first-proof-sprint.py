#!/usr/bin/env python3
"""Assemble converted APM informal proofs into one First Proof Sprint document.

Reads the .tex produced by informal-proofs-to-tex.sh, pairs each with its
problem statement, and writes a master document ready for lualatex.
"""
from __future__ import annotations

import argparse
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


def heading_end(body: str) -> int | None:
    """Index just past the chapter heading, counting braces rather than matching
    a regex: pandoc wraps titles in \\texorpdfstring{..}{..}, so a non-greedy
    \\chapter\\{.*?\\} stops at the first inner brace and splits the macro."""
    i = body.find(r"\chapter{")
    if i < 0:
        return None
    j = i + len(r"\chapter{")
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


PREAMBLE = r"""\documentclass[11pt,oneside]{book}
\usepackage[margin=1.1in]{geometry}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage[dvipsnames]{xcolor}
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
    args = ap.parse_args()

    ids = [x.strip() for x in Path(args.id_list).read_text().split() if x.strip()]
    tex_dir = Path(args.tex_dir)
    parts = [PREAMBLE.replace("@NPROOFS@", str(len(ids)))
                 .replace("@TOTAL@", str(args.total))]
    folded_total = 0

    for pid in ids:
        body_path = tex_dir / f"apm-{pid}.tex"
        if not body_path.is_file():
            print(f"missing converted proof: {body_path}", file=sys.stderr)
            return 1
        body, folded = fold_combining(body_path.read_text())
        folded_total += folded

        # The converter emits \section for the proof title; promote to \chapter
        # so each proof is a top-level unit of the sample.
        body = re.sub(r"\\section\{", r"\\chapter{", body, count=1)
        body = body.replace(r"\subsection{", r"\section{")
        body = body.replace(r"\subsubsection{", r"\subsection{")

        stmt_path = REPO_ROOT / "problems" / pid / "problem.tex"
        stmt = stmt_path.read_text().strip() if stmt_path.is_file() else ""

        # Insert the problem statement directly under the chapter heading, so a
        # reader meets the question before the answer. pandoc wraps the heading
        # as \hypertarget{..}{%\n\\chapter{..}\\label{..}}; split after that block.
        if stmt:
            block = "\n\\begin{problemstatement}\n" + stmt + "\n\\end{problemstatement}\n"
            cut = heading_end(body)
            if cut is not None:
                body = body[:cut] + "\n" + block + body[cut:]
            else:
                body = block + body

        parts.append(f"\n%% ==== {pid} ====\n")
        parts.append(body)
        parts.append(f"\n\\chaptermark{{APM {pid}}}\n")

    parts.append("\n\\end{document}\n")
    Path(args.out).write_text("".join(parts))
    print(f"Wrote {args.out} ({len(ids)} proofs, {folded_total} combining accents folded)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
