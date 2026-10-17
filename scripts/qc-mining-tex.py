#!/usr/bin/env python3
"""Count conversion defects in exported mining papers, before any mining.

The first mark8 run over the APM proofs (2026-10-16) went to a rented GPU with
papers that compiled cleanly and still read badly: formulae set as verbatim
code (`\\sigma_a = \\rho(a)` as \\texttt with literal backslashes), formulae cut
in two ($1/(2\\pi$in$^{2}$), shown by LaTeXML as CLOSE), escaped _ and ^ in
prose. Compiling is not reading. This counts each defect class over the
papers' text, prints examples, and exits non-zero when any class exceeds its
allowance, so the export is checked before money is spent on it.

Usage: qc-mining-tex.py <eprints-dir> [--examples N] [--max-per-paper F]
"""
from __future__ import annotations

import argparse
import collections
import re
import sys
from pathlib import Path

PATH_LIKE = re.compile(r"(?:[\w.-]+/)+[\w.\\-]+")       # ApmCanaries/Frames/.../Main


def math_spans(text: str):
    """(start, end, inner) of $...$ and \\(...\\) spans; the same rule as S1."""
    i, n = 0, len(text)
    while i < n:
        if text.startswith("\\(", i):
            j = text.find("\\)", i + 2)
            if j < 0:
                return
            yield i, j + 2, text[i + 2:j]
            i = j + 2
        elif text[i] == "$" and (i == 0 or text[i - 1] != "\\"):
            if text.startswith("$$", i):
                j = text.find("$$", i + 2)
                if j < 0:
                    return
                i = j + 2
                continue
            j = i + 1
            while j < n and not (text[j] == "$" and text[j - 1] != "\\"):
                j += 1
            if j >= n:
                return
            yield i, j + 1, text[i + 1:j]
            i = j + 1
        else:
            i += 1


def defects(body: str) -> dict[str, list[str]]:
    found: dict[str, list[str]] = collections.defaultdict(list)
    spans = list(math_spans(body))
    prose = list(body)
    for a, b, _ in spans:
        prose[a:b] = " " * (b - a)
    prose = "".join(prose)
    prose = re.sub(r"%[^\n]*", " ", prose)
    prose_text = re.sub(r"\\texttt\{(?:[^{}]|\{[^{}]*\})*\}", " ", prose)
    prose_text = PATH_LIKE.sub(" ", prose_text)

    def ctx(text, m):
        return text[max(0, m.start() - 40):m.end() + 40].replace("\n", " ")

    for m in re.finditer(r"\\texttt\{(?:[^{}]|\{[^{}]*\})*\\textbackslash\{\}[A-Za-z]", body):
        found["formula set as code (LaTeX inside \\texttt)"].append(ctx(body, m))
    for m in re.finditer(r"\\texttt\{(?:\d+|[A-Za-z])\}", body):
        found["single symbol set as code (\\texttt{f})"].append(ctx(body, m))
    for m in re.finditer(r"\\textbackslash\{?\}?[A-Za-z]", prose_text):
        found["LaTeX command as text (\\textbackslash)"].append(ctx(prose_text, m))
    for m in re.finditer(r"[A-Za-z0-9}]\\_|\\\^\{\}", prose_text):
        found["escaped _ or ^ in prose"].append(ctx(prose_text, m))
    for m in re.finditer(r"\*\*[^*\n]+\*\*", prose):
        found["markdown bold left over (**x**)"].append(ctx(prose, m))
    for a, b, inner in spans:
        if not inner.strip():
            found["empty formula"].append(body[max(0, a - 40):b + 40].replace("\n", " "))
            continue
        if inner.count("(") - inner.count(")") + inner.count("[") - inner.count("]"):
            found["formula with unbalanced brackets"].append(body[max(0, a - 30):b + 30].replace("\n", " "))
        if re.match(r"[A-Za-z]", body[b:b + 1]) and re.search(r"[A-Za-z0-9}]$", inner):
            found["formula ending against a letter"].append(body[max(0, a - 30):b + 30].replace("\n", " "))
    return found


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("eprints")
    ap.add_argument("--examples", type=int, default=3)
    ap.add_argument("--max-per-paper", type=float, default=0.5,
                    help="allowance: defects of one class per paper, on average")
    args = ap.parse_args()
    papers = sorted(p for p in Path(args.eprints).glob("*.tex"))
    totals: collections.Counter = collections.Counter()
    where: dict[str, set] = collections.defaultdict(set)
    examples: dict[str, list] = collections.defaultdict(list)
    for p in papers:
        text = p.read_text(errors="replace")
        body = text[text.find("\\begin{document}"):]
        for name, hits in defects(body).items():
            totals[name] += len(hits)
            where[name].add(p.stem)
            if len(examples[name]) < args.examples:
                examples[name].append(f"{p.stem}: {hits[0]}")
    allowance = args.max_per_paper * len(papers)
    failed = False
    print(f"{len(papers)} papers")
    for name, n in totals.most_common():
        over = n > allowance
        failed |= over
        print(f"{'FAIL' if over else 'ok  '} {n:6d} in {len(where[name]):3d} papers  {name}")
        for e in examples[name]:
            print(f"         {e}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
