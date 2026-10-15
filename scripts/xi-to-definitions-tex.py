#!/usr/bin/env python3
"""Render the Xi concept list as a LaTeX paper of definitions, for futon6 WARP.

WARP's definition pass collects a corpus's concepts from definition
environments. The APM proofs define almost nothing, so S2 grounded no concept;
Xi (Joe Corneli, 2002-2003) is the concept index written for these problems.
Rendered as one more paper in the eprint store -- and left out of the id list
the mining stages read -- it gives WARP its definitions without being mined.

Each Xi definition becomes
    \\begin{definition}\\emph{bounded variation}: ... conditions ...\\end{definition}
under its Xi heading, with the problems Xi links to that heading.

Usage: xi-to-definitions-tex.py <xi-concepts.json> <Xi.tex> <out.tex>
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

HEAD = r"""\documentclass[11pt]{article}
\usepackage{amsmath,amssymb,amsthm,stmaryrd}
\usepackage[mathscr]{euscript}
\newtheorem{definition}{Definition}
"""
TAIL = r"""
\title{Xi: a concept index for the APM problems}
\author{Joseph Corneli (2002--2003)}
\date{}
\begin{document}
\maketitle
"""
# Packages and layout from Xi's own preamble that this rendering does not need
# (fonts, margins, pictures); its macro definitions are kept as written.
DROP = re.compile(r"\\(?:usepackage|documentclass|set(?:left|right|top|bottom)margin)\b")


def xi_macros(xi_tex: str) -> str:
    pre = xi_tex[:xi_tex.index("\\begin{document}")]
    pre = pre[pre.index("\\documentclass"):]
    keep = [line for line in pre.split("\n") if not DROP.search(line)]
    return "\n".join(keep)


def clean(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def main() -> int:
    src, xi_tex, out = sys.argv[1], sys.argv[2], sys.argv[3]
    d = json.loads(Path(src).read_text())
    parts = [HEAD, xi_macros(Path(xi_tex).read_text(encoding="latin-1")), TAIL]
    for sec in d["sections"]:
        if not sec["heading"]:
            continue
        parts.append(f"\n\\section{{{clean(sec['heading'])}}}\n")
        for df in sec["definitions"]:
            conds = "".join(f"\n  \\item {clean(c)}" for c in df["conditions"])
            body = f"\\begin{{itemize}}{conds}\n\\end{{itemize}}" if conds else ""
            parts.append(f"\\begin{{definition}}\\emph{{{clean(df['term'])}}}: {body}\n"
                         f"\\end{{definition}}\n")
        for note in sec["notes"]:
            if note["text"]:
                parts.append(f"\\noindent\\emph{{{clean(note['term'])}}} "
                             f"({note['kind']}): {clean(note['text'])}\n\n")
        if sec["problems"]:
            ids = ", ".join(p["id"] for p in sec["problems"])
            parts.append(f"\\noindent Problems: {ids}.\n")
    parts.append("\n\\end{document}\n")
    Path(out).write_text("".join(parts))
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
