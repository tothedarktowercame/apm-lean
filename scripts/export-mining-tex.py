#!/usr/bin/env python3
"""Write each converted APM proof as a standalone paper for futon6 mining.

Reads the apm-<id>.tex bodies made by informal-proofs-to-tex.sh and writes one
compilable document per problem, <out>/<id>.tex, the flat layout futon6's
$FUTON6_EPRINTS store reads. The book (build-first-proof-sprint.py) is for
reading; this is for parsing, so it differs in what it keeps:

- the problem statement becomes \\begin{problem}..\\end{problem};
- the section that holds the proof goes inside \\begin{proof}..\\end{proof},
  so the anatomy pass finds a proof attached to the statement;
- the sections around it ("Why It's Hard", "The Key Insight", "What Connects")
  stay as sections, i.e. as exposition;
- Lean material (theorem statements, Mathlib cross-references, highlighted Lean
  code, the margin links to Lean declarations) is dropped: it is not proof prose;
- the syntax-class wrappers (\\mNumber{0} and friends) are unwrapped.

The proofs come in three shapes. "Complete Proof" and "1. Informal proof" name
the proof section outright; a proof with neither has its whole body wrapped.
The shape of each one is recorded in <out>/manifest.json, so results can be
read per shape.

Usage: export-mining-tex.py <id-list> <tex-dir> <out-dir>
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Section titles (as pandoc writes them) that name the proof proper.
PROOF_TITLES = {"Complete Proof", "1. Informal proof", "Informal proof",
                "Proof", "Complete proof"}
# Section titles whose content is Lean apparatus, not mathematics.
DROP_TITLE = re.compile(r"Lean|Mathlib", re.I)

HEADING = re.compile(r"\\(section|subsection|subsubsection|paragraph)\*?\{")
LEVEL = {"section": 1, "subsection": 2, "subsubsection": 3, "paragraph": 4}


def macro_block() -> str:
    """The APM statement macros, taken from the book's preamble so the two
    documents cannot drift apart."""
    spec = importlib.util.spec_from_file_location(
        "build_fps", REPO_ROOT / "scripts" / "build-first-proof-sprint.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    pre = mod.PREAMBLE
    start = pre.index("% APM problem-statement macros")
    end = pre.index("\\newenvironment{problemstatement}")
    return pre[start:end].rstrip() + "\n"


PREAMBLE = r"""\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{enumitem,longtable,booktabs,xcolor}
\newenvironment{alist}{\begin{enumerate}[label=(\alph*)]}{\end{enumerate}}
\newenvironment{rlist}{\begin{enumerate}[label=(\roman*)]}{\end{enumerate}}
\newenvironment{123list}{\begin{enumerate}[label=(\arabic*)]}{\end{enumerate}}
\newenvironment{Rlist}{\begin{enumerate}[label=(\Roman*)]}{\end{enumerate}}
\providecommand{\T}{\mathbb{T}}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\providecommand{\texorpdfstring}[2]{#1}
\providecommand{\hypertarget}[2]{#2}
\providecommand{\mathup}{\mathrm}
\newtheorem{problem}{Problem}
@MACROS@
\title{APM @ID@}
\date{}
\begin{document}
\maketitle
"""


def group_end(s: str, i: int) -> int:
    """Index just past the brace group opening at s[i] == '{'."""
    depth = 0
    j = i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    raise ValueError(f"unbalanced group at {i}")


def unwrap(s: str, name: str, keep: str | None) -> str:
    """Replace every \\name{X} by keep.format(X), or delete it if keep is None."""
    pat = re.compile(r"\\" + name + r"\{")
    out, pos = [], 0
    for m in pat.finditer(s):
        if m.start() < pos:
            continue
        end = group_end(s, m.end() - 1)
        inner = s[m.end():end - 1]
        out.append(s[pos:m.start()])
        if keep is not None:
            out.append(keep.replace("#", inner))
        pos = end
    out.append(s[pos:])
    return "".join(out)


def clean(body: str) -> str:
    body = re.sub(r"\\begin\{Shaded\}.*?\\end\{Shaded\}",
                  "% [Lean code omitted]", body, flags=re.S)
    body = unwrap(body, "apmlink", None)
    # pandoc's \hypertarget{id}{%\n\section{..}\label{..}} around each heading
    body = re.sub(r"\\hypertarget\{[^{}]*\}\{%\n", "", body)
    body = re.sub(r"(\\label\{[^{}]*\})\}", r"\1", body)
    body = unwrap(body, "mOpName", r"\operatorname{#}")
    # pandoc-mathify writes integrals as \Integral, which only the book's
    # math-proofread-style.sty defines (as \int).
    body = re.sub(r"\\(?:I|i)ntegral(?![A-Za-z])", r"\\int", body)
    # The one argumentless class macro: a dual/cotangent star, T^{\mDualStar}M.
    body = re.sub(r"\\mDualStar(?![A-Za-z])", r"\\ast{}", body)
    # Unwrap innermost-first so nested wrappers all go.
    for _ in range(4):
        before = body
        for name in ("mNumber", "mConstant", "mExponent", "mSubscript", "mGreek",
                     "mOperator", "mBridgeOperator", "mRelation", "mCompare",
                     "mLargeOperator", "mArrow", "mDelimiter", "mFunction",
                     "mMathText", "mMathItalic"):
            body = unwrap(body, name, "{#}")
        if body == before:
            break
    # pandoc already braced most wrapped atoms ("{\mNumber{0}}"), so the
    # unwrapped form is "{{0}}"; one pair is enough.
    while True:
        collapsed = re.sub(r"\{\{([^{}]*)\}\}", r"{\1}", body)
        if collapsed == body:
            break
        body = collapsed
    # A braced number standing alone needs no braces ("e^{{2}\pi iz}", "${0} < x$");
    # an argument does ("\frac{1}{2}", "x_{10}"), so only after a space, an
    # operator, an opening bracket or "$".
    body = re.sub(r"(?<=[\s(\[=+\-*/,<>{$])\{(\d+(?:\.\d+)?)\}", r"\1", body)
    # Headings carry \texorpdfstring{TeX}{plain}; the papers load no hyperref, so
    # the plain copy (with \_ and \textbackslash for every symbol) is only noise
    # in front of the miners: 1,192 of them in the APM export.
    body = unwrap_first_of_two(body, "texorpdfstring")
    return body


def unwrap_first_of_two(s: str, name: str) -> str:
    """Replace every \\name{A}{B} by A."""
    pat = re.compile(r"\\" + name + r"\{")
    out, pos = [], 0
    for m in pat.finditer(s):
        if m.start() < pos:
            continue
        first_end = group_end(s, m.end() - 1)
        if first_end < 0 or first_end >= len(s) or s[first_end] != "{":
            continue
        second_end = group_end(s, first_end)
        if second_end < 0:
            continue
        out.append(s[pos:m.start()])
        out.append(s[m.end():first_end - 1])
        pos = second_end
    out.append(s[pos:])
    return "".join(out)


def dollar_inline(text: str) -> str:
    r"""Write inline math as $...$ rather than \(...\).

    The two are the same to LaTeX, but futon6's anatomy pass (S1) was built on
    arXiv sources, which mostly use dollars. Measured on a00J02 (2026-10-15):
    with \(...\) S1 found 12 clause units (bind/let, constrain/relation, ...),
    with $...$ it found 53, and IATC candidates need those units as spans; five
    of the sixteen pilot proofs were refused at the precheck for having none.
    """
    return re.sub(r"\\\((.*?)\\\)", lambda m: "$" + m.group(1) + "$", text, flags=re.S)


def sections(body: str) -> list[dict]:
    """Split a body at its headings: [{level, title, head, text}], where the
    first entry (level 0) is whatever precedes the first heading."""
    marks = []
    for m in HEADING.finditer(body):
        end = group_end(body, m.end() - 1)
        title = body[m.end():end - 1]
        lab = re.match(r"\\label\{[^{}]*\}", body[end:])
        hend = end + (lab.end() if lab else 0)
        marks.append((m.start(), hend, LEVEL[m.group(1)], title))
    out = [{"level": 0, "title": "", "head": "",
            "text": body[:marks[0][0]] if marks else body}]
    for k, (s, hend, lvl, title) in enumerate(marks):
        nxt = marks[k + 1][0] if k + 1 < len(marks) else len(body)
        out.append({"level": lvl, "title": title, "head": body[s:hend],
                    "text": body[hend:nxt]})
    return out


def runin_headings(text: str) -> str:
    """A sectioning command cannot open inside a proof environment (TeX stops
    with "Improper \\prevdepth" or "missing \\item"), so headings that fall
    inside a proof become bold run-in labels."""
    out, pos = [], 0
    for m in HEADING.finditer(text):
        if m.start() < pos:
            continue
        end = group_end(text, m.end() - 1)
        lab = re.match(r"\\label\{[^{}]*\}", text[end:])
        out.append(text[pos:m.start()])
        out.append("\\par\\medskip\\noindent\\textbf{" + text[m.end():end - 1] + "}\\par\n")
        pos = end + (lab.end() if lab else 0)
    out.append(text[pos:])
    return "".join(out)


def plain_title(t: str) -> str:
    t = re.sub(r"\\textquotesingle\s*", "'", t)
    return re.sub(r"\s+", " ", t).strip()


def restructure(body: str) -> tuple[str, str]:
    """Return (document body, shape)."""
    secs = sections(body)
    # The first heading is the proof's own title ("Informal Solution: a00J01");
    # \title carries the id, so drop it.
    if len(secs) > 1 and secs[0]["text"].strip() == "":
        top = secs[1]["level"]
        if re.search(r"Informal Solution|^APM|solution", plain_title(secs[1]["title"]), re.I):
            secs = [secs[0], {**secs[1], "head": ""}] + secs[2:]
    else:
        top = min((s["level"] for s in secs[1:]), default=1)

    # Drop Lean sections together with their subsections.
    kept, drop_below = [], None
    for s in secs:
        if drop_below is not None and s["level"] > drop_below:
            continue
        drop_below = None
        if s["level"] and DROP_TITLE.search(plain_title(s["title"])):
            drop_below = s["level"]
            continue
        kept.append(s)

    idx = next((k for k, s in enumerate(kept)
                if plain_title(s["title"]) in PROOF_TITLES), None)
    if idx is None:
        text = "".join(s["head"] + s["text"] for s in kept)
        # The proof-frame write-ups mark their parts in bold: "Stage 1 --- THE
        # CLEAN PROOF", then lemma graphs, critiques and so on. Stage 1 is the
        # proof; the later stages are commentary on it.
        st1 = re.search(r"\\textbf\{Stage 1 ---[^{}]*\}", text)
        st2 = re.search(r"\\textbf\{Stage 2 ---", text)
        if st1 and st2 and st2.start() > st1.end():
            return (text[:st1.start()] + "\\section*{Proof}\n\\begin{proof}\n"
                    + runin_headings(text[st1.end():st2.start()]).strip() + "\n\\end{proof}\n\n"
                    + "\\section*{Commentary}\n" + text[st2.start():], "stages")
        return "\\begin{proof}\n" + runin_headings(text).strip() + "\n\\end{proof}\n", "unstructured"

    lvl = kept[idx]["level"]
    end = next((k for k in range(idx + 1, len(kept)) if kept[k]["level"] <= lvl),
               len(kept))
    before = "".join(s["head"] + s["text"] for s in kept[:idx])
    proof = kept[idx]["text"] + "".join(s["head"] + s["text"] for s in kept[idx + 1:end])
    after = "".join(s["head"] + s["text"] for s in kept[end:])
    shape = "complete-proof" if plain_title(kept[idx]["title"]) == "Complete Proof" else "informal-proof"
    doc = (before + kept[idx]["head"] + "\n\\begin{proof}\n" + runin_headings(proof).strip()
           + "\n\\end{proof}\n" + after)
    return doc, shape


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("id_list")
    ap.add_argument("tex_dir")
    ap.add_argument("out_dir")
    args = ap.parse_args()
    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    macros = macro_block()
    manifest = {}
    for pid in Path(args.id_list).read_text().split():
        body_path = Path(args.tex_dir) / f"apm-{pid}.tex"
        stmt_path = REPO_ROOT / "problems" / pid / "problem.tex"
        if not body_path.is_file() or not stmt_path.is_file():
            print(f"{pid}: missing {body_path if not body_path.is_file() else stmt_path}",
                  file=sys.stderr)
            return 1
        body, shape = restructure(clean(body_path.read_text()))
        body = dollar_inline(body)
        stmt = dollar_inline(clean(stmt_path.read_text()).strip())
        doc = (PREAMBLE.replace("@MACROS@", macros).replace("@ID@", pid)
               + "\n\\begin{problem}\n" + stmt + "\n\\end{problem}\n\n"
               + body + "\n\\end{document}\n")
        bad = sorted({c for c in doc if ord(c) > 127})
        if bad:
            print(f"{pid}: non-ASCII left: {''.join(bad)}", file=sys.stderr)
            return 1
        (out / f"{pid}.tex").write_text(doc)
        manifest[pid] = {"shape": shape}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=1, sort_keys=True) + "\n")
    counts: dict[str, int] = {}
    for v in manifest.values():
        counts[v["shape"]] = counts.get(v["shape"], 0) + 1
    print(f"Wrote {len(manifest)} papers to {out}: {counts}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
