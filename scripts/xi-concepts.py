#!/usr/bin/env python3
"""Read Xi.tex (Joe Corneli, 2002-2003) into a structured concept list.

Xi is a concept index for the APM problems, written "in a LISP-like style" so
that it could later be parsed (its own header says so). Each \\section is a
concept heading; inside it,

    (bounded variation) \\defn{ \\item $f: \\R\\rightarrow \\C$ \\item ... }
    (tangent bundle of a manifold: notation: $TX$)
    (smooth structure on tangent bundle: fact: $\\psi$ is a homeomorphism)
    \\prob{a93J01}{(2.3.1)}

a parenthesised name followed by \\defn{...} is a definition whose \\items are
its conditions; a parenthesised name alone is a note (notation, fact, or a
term named but not yet defined); \\prob links a problem by its APM id.

Usage: xi-concepts.py <Xi.tex> <out.json> [--ids <corpus-ids>]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

SECTION = re.compile(r"\\section\*?(?=\{)")
PROB = re.compile(r"\\prob\{([^{}]+)\}\{([^{}]*)\}")


def strip_comments(text: str) -> str:
    return "\n".join(re.sub(r"(?<!\\)%.*", "", line) for line in text.split("\n"))


def group_end(s: str, i: int) -> int:
    """Index just past the brace group opening at s[i] == '{', or -1."""
    depth, j = 0, i
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
    return -1


def paren_end(s: str, i: int) -> int:
    """Index just past the parenthesised name opening at s[i] == '(', or -1.
    Math inside the name ($TX$, $(a,b)$) may hold parentheses of its own."""
    depth, j, in_math = 0, i, False
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == "$":
            in_math = not in_math
        elif not in_math and c == "(":
            depth += 1
        elif not in_math and c == ")":
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return -1


def items(body: str) -> list[str]:
    parts = re.split(r"\\item\b", body)
    return [re.sub(r"\s+", " ", p).strip() for p in parts[1:] if p.strip()]


def parse_section(title: str, body: str) -> dict:
    defs, notes = [], []
    i = 0
    while True:
        k = body.find("(", i)
        if k < 0:
            break
        # A name opens a line (possibly after spaces); a "(" mid-sentence or
        # inside math is not a name.
        line_start = body.rfind("\n", 0, k) + 1
        if body[line_start:k].strip():
            i = k + 1
            continue
        e = paren_end(body, k)
        if e < 0:
            break
        name = re.sub(r"\s+", " ", body[k + 1:e - 1]).strip()
        rest = body[e:]
        m = re.match(r"\s*\\defn\{", rest)
        if m:
            g = group_end(body, e + m.end() - 1)
            if g < 0:
                break
            defs.append({"term": name, "conditions": items(body[e + m.end():g - 1])})
            i = g
        else:
            kind = "note"
            mm = re.match(r"(.*?):\s*(notation|fact|example|theorem|lemma|remark)\s*:\s*(.*)$",
                          name, re.S)
            if mm:
                notes.append({"term": mm.group(1).strip(), "kind": mm.group(2),
                              "text": mm.group(3).strip()})
            else:
                notes.append({"term": name, "kind": kind, "text": ""})
            i = e
    probs = [{"id": p, "ref": r.strip("() ")} for p, r in PROB.findall(body)]
    return {"heading": title.strip(), "definitions": defs, "notes": notes, "problems": probs}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("xi")
    ap.add_argument("out")
    ap.add_argument("--ids", help="corpus id list, to report coverage")
    args = ap.parse_args()
    text = strip_comments(Path(args.xi).read_text(encoding="latin-1"))
    text = text[text.find("\\begin{document}"):]
    # A heading is a brace group that may hold braces of its own, e.g.
    # \section{{cover (not \emph{covering})}}, so match it, don't regex it.
    heads = []
    for m in SECTION.finditer(text):
        g = group_end(text, m.end())
        if g > 0:
            title = text[m.end() + 1:g - 1].strip()
            while title.startswith("{") and group_end(title, 0) == len(title):
                title = title[1:-1].strip()
            heads.append((m.start(), g, title))
    sections = []
    for n, (_start, g, title) in enumerate(heads):
        end = heads[n + 1][0] if n + 1 < len(heads) else len(text)
        sections.append(parse_section(title, text[g:end]))
    doc = {"schema": "xi-concepts/v1", "source": "Xi.tex (J. Corneli, 2002-2003)",
           "sections": sections}
    Path(args.out).write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n")
    nd = sum(len(s["definitions"]) for s in sections)
    nn = sum(len(s["notes"]) for s in sections)
    linked = {p["id"] for s in sections for p in s["problems"]}
    print(f"{len(sections)} sections, {nd} definitions, {nn} notes, "
          f"{sum(len(s['problems']) for s in sections)} problem links "
          f"({len(linked)} distinct problems)")
    if args.ids:
        ids = set(Path(args.ids).read_text().split())
        print(f"corpus coverage: {len(linked & ids)}/{len(ids)} problems linked; "
              f"linked but not in corpus: {sorted(linked - ids)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
