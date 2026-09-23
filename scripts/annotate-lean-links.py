#!/usr/bin/env python3
"""Link names in the informal proof to the Lean proof that uses them.

The Tufte margin beside the informal argument was empty. This fills it from the
one bridge between the two registers that can be computed exactly, with no
model of what the mathematics means: the informal proofs already name Mathlib
results in code spans -- `Real.sqrt`, `MeasurePreserving`,
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` -- and those names either are
declarations of the problem's own Lean proof or appear inside one. A name is a
name; matching it is not an inference.

Over the corpus that is 944 anchors across 275 of the 488 proofs that have a
Lean file, counting each name once per proof, at its first mention.

Each anchor becomes an \\apmlink, which the preamble makes a \\footnote and
tuftify turns into a numbered Tufte sidenote. Numbered rather than a bare
margin note on purpose: the note is keyed to one word, so the reader needs to
see which.

What this does NOT do is say what a step MEANS -- that "the fat Cantor set" of
the prose is `apm_a94J02_exists_fat_compact` in the Lean. That mapping needs
the scope-mining work, and arrives through report/lean-annotations.json.
See docs/TN-lean-margin-annotations.md.

Operates on generated .tex; sources are never touched.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

from leanfile import DECL_START, docstring, segment, uses
from texcode import CODE_OR_TABLE, map_outside_code

REPO_ROOT = Path(__file__).resolve().parent.parent

# \texttt{..} as pandoc emits it: the body may contain escaped specials and
# escaped spaces, but no nested groups.
TEXTTT = re.compile(r"\\texttt\{((?:[^{}\\]|\\[\\_&%#{}~^]|\\ )+)\}")
UNESCAPE = re.compile(r"\\([\\_&%#{}~^ ])")

# A footnote inside a sectioning command breaks the heading and the table of
# contents; skip any match on a line that carries one.
HEADING = re.compile(r"\\(?:sub)*section\*?\{|\\texorpdfstring|\\hypertarget")

MAX_DECLS = 3

# report/lean4.xml already lists Lean's keywords and the tactic vocabulary, for
# highlighting. Reuse it as the stop list rather than keeping a second copy:
# "The Lean proof invokes linarith in the step ..." is true and useless -- the
# margin is for the mathematics, not for how the tactic block was driven.
def stop_words() -> set[str]:
    import xml.etree.ElementTree as ET
    root = ET.parse(REPO_ROOT / "report" / "lean4.xml").getroot()
    return {item.text.strip()
            for lst in root.iter("list")
            for item in lst.iter("item") if item.text}


STOP = stop_words()


def latex_escape(text: str) -> str:
    for a, b in (("\\", r"\textbackslash{}"), ("{", r"\{"), ("}", r"\}"),
                 ("$", r"\$"), ("&", r"\&"), ("#", r"\#"), ("%", r"\%"),
                 ("_", r"\_"), ("^", r"\^{}"), ("~", r"\textasciitilde{}")):
        text = text.replace(a, b)
    return text


def mono(name: str) -> str:
    return "\\texttt{" + latex_escape(name) + "}"


def note_for(name: str, decls: dict[str, dict], used_by: dict[str, list[str]]) -> str | None:
    """What the margin should say about this name, or None if nothing exact."""
    if name in STOP:
        return None
    if name in decls:
        doc = docstring(decls[name])
        lead = f"Formalised in this problem's Lean proof as {mono(name)}."
        return lead + (" " + latex_escape(doc) if doc else "")
    where = used_by.get(name)
    if not where:
        return None
    shown = [mono(d) for d in where[:MAX_DECLS]]
    more = "" if len(where) <= MAX_DECLS else f", and {len(where) - MAX_DECLS} more"
    verb = "step" if len(shown) == 1 else "steps"
    return (f"The Lean proof invokes {mono(name)} in the {verb} "
            + ", ".join(shown) + more + ".")


def linked_ranges(text: str) -> list[tuple[int, int]]:
    """Spans already occupied by an \\apmlink note.

    A note contains \\texttt groups of its own, so without this a second run
    annotates the first run's notes. The pipeline regenerates the .tex each
    time and would not hit it, but a hand re-run should be a no-op."""
    out, i = [], 0
    while True:
        i = text.find("\\apmlink{", i)
        if i < 0:
            return out
        j, depth = i + 9, 1
        while j < len(text) and depth:
            if text[j] == "\\":
                j += 2
                continue
            depth += (text[j] == "{") - (text[j] == "}")
            j += 1
        out.append((i, j))
        i = j


def annotate(body: str, lean_src: str) -> tuple[str, int]:
    chunks = segment(lean_src.split("\n"))
    decls = {c["name"]: c for c in chunks if c["name"]}
    used_by = uses(chunks)
    seen: set[str] = set()

    def pass_over(text: str) -> tuple[str, int]:
        out, pos, n = [], 0, 0
        taken = linked_ranges(text)
        for m in TEXTTT.finditer(text):
            name = UNESCAPE.sub(r"\1", m.group(1)).strip()
            if name in seen:
                continue
            if any(a <= m.start() < b for a, b in taken):
                continue
            if text.startswith("\\apmlink{", m.end()):
                seen.add(name)      # already annotated; a re-run is a no-op
                continue
            line_start = text.rfind("\n", 0, m.start()) + 1
            line_end = text.find("\n", m.end())
            if HEADING.search(text[line_start: line_end if line_end > 0 else len(text)]):
                continue
            note = note_for(name, decls, used_by)
            if not note:
                continue
            seen.add(name)
            out.append(text[pos:m.end()])
            out.append("\\apmlink{" + note + "}")
            pos = m.end()
            n += 1
        out.append(text[pos:])
        return "".join(out), n

    return map_outside_code(body, pass_over, CODE_OR_TABLE)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="+", help="generated apm-<id>.tex files")
    ap.add_argument("--problems", default=str(REPO_ROOT / "problems"))
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()

    problems = Path(args.problems)
    total = files = 0
    for p in sorted(Path(x) for x in args.paths):
        pid = p.stem[4:] if p.stem.startswith("apm-") else p.stem
        lean = problems / pid / "lean" / "Main.lean"
        if not lean.is_file():
            continue
        fixed, n = annotate(p.read_text(), lean.read_text())
        if n:
            total += n
            files += 1
            if args.write:
                p.write_text(fixed)
    print(f"Linked {total} name(s) to their Lean proof in {files} file(s)"
          + ("" if args.write else " (dry run; pass --write)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
