#!/usr/bin/env python3
"""Render each problem's Lean proof to a highlighted LaTeX fragment.

Output is one <out-dir>/lean/apm-<id>.tex per problem, which
build-first-proof-sprint.py appends as a section below the informal argument.
The subdirectory matters: the conversion pipeline's repair passes glob
apm-*.tex in the output directory, and a Lean listing must not be run through
math-span repair.

Three things happen here that are worth knowing about:

1.  HIGHLIGHTING.  Neither pandoc nor KSyntaxHighlighting ships a Lean syntax
    definition, so pandoc emitted every line as one \\NormalTok.  report/lean4.xml
    supplies one; it colours claims (green), tactics (blue) and `sorry` (red),
    which is enough to read the shape of a proof without knowing Lean.

2.  SEGMENTING.  The file is cut at top-level declarations rather than shipped
    as one listing, so each declaration can carry its own margin note.

3.  THE MARGIN APPARATUS.  Each declaration gets a \\marginpar naming the
    earlier lemmas in the same file that it reuses.  That is an exact
    computation over declaration names, not an inference: it says how the proof
    hangs together, which is the part of "how the Lean concepts relate" that can
    be known without a concept model.

    The informal-to-formal concept mapping proper -- which phrase in the prose
    corresponds to which Mathlib lemma -- is NOT computed here.  It waits on the
    scope-mining work.  The apparatus reads it from report/lean-annotations.json
    when that file exists, keyed "<problem id>/<declaration name>", so populating
    it later needs no change to this script.  Two author-supplied sources are
    already wired in: that JSON, and the "Mathlib cross-refs" line that 62 of the
    informal solutions carry, which becomes the section's opening margin note.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SYNTAX = REPO_ROOT / "report" / "lean4.xml"
ANNOTATIONS = REPO_ROOT / "report" / "lean-annotations.json"

DECL_KINDS = (
    "theorem|lemma|def|abbrev|instance|structure|class|inductive|example|"
    "axiom|opaque"
)
MODIFIERS = r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
# A top-level declaration starts in column 0. Anything indented is inside a
# proof -- `have`, a nested `def` in a `let rec`, a tactic block.
DECL_START = re.compile(rf"^(?:@\[[^\]]*\]\s*)?{MODIFIERS}({DECL_KINDS})\s+([^\s:({{\[]+)")
DOC_START = re.compile(r"^/--")
ATTR_START = re.compile(r"^@\[")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*")

SORRY = re.compile(r"(?<![\w.'])sorry(?![\w'])")
CROSSREFS = re.compile(
    r"^\s*\*\*Mathlib cross-refs?:?\*\*\s*(.+?)$", re.M | re.I)


def segment(lines: list[str]) -> list[dict]:
    """Cut a Lean file into a header plus one chunk per top-level declaration.

    A chunk opens at a column-0 docstring, attribute or declaration keyword and
    runs to the next one, so a declaration keeps its own docstring, attributes
    and proof body together."""
    starts = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if DOC_START.match(line) or ATTR_START.match(line) or DECL_START.match(line):
            # A docstring or attribute opens the chunk its declaration belongs
            # to; do not open a second chunk at the declaration itself.
            if not starts or starts[-1][1] < i:
                starts.append((i, i))
            j = i
            # Advance past the docstring/attribute to find the declaration name.
            while j < len(lines) and not DECL_START.match(lines[j]):
                j += 1
                if j - i > 60:       # runaway: treat the opener as the chunk
                    break
            starts[-1] = (starts[-1][0], j)
            i = j + 1
            continue
        i += 1

    chunks = []
    if not starts:
        return [{"name": None, "kind": None, "lines": lines}]
    if starts[0][0] > 0:
        chunks.append({"name": None, "kind": None, "lines": lines[: starts[0][0]]})
    for n, (begin, declline) in enumerate(starts):
        end = starts[n + 1][0] if n + 1 < len(starts) else len(lines)
        m = DECL_START.match(lines[declline]) if declline < len(lines) else None
        chunks.append({
            "kind": m.group(1) if m else None,
            "name": m.group(2) if m else None,
            "lines": lines[begin:end],
        })
    return chunks


def latex_escape(text: str) -> str:
    out = text
    for a, b in (("\\", r"\textbackslash{}"), ("{", r"\{"), ("}", r"\}"),
                 ("$", r"\$"), ("&", r"\&"), ("#", r"\#"), ("%", r"\%"),
                 ("_", r"\_"), ("^", r"\^{}"), ("~", r"\textasciitilde{}")):
        out = out.replace(a, b)
    return out


# A paragraph pandoc will pass through untouched, so one call can highlight a
# whole file's worth of chunks and the output be cut back apart. Per-chunk calls
# meant 6,730 pandoc invocations for the corpus instead of 488.
SPLIT_MARK = "XAPMCHUNKSPLITX"
SPLIT_RE = re.compile(r"^" + SPLIT_MARK + r"$", re.M)


def code_to_latex(chunks: list[str]) -> list[str]:
    """Highlight through pandoc, which is also what converts the informal
    markdown, so the two listings on a page are typeset the same way.

    Six backticks, not three: Lean quotes names with a backtick and a fence
    only has to be longer than any backtick run inside it."""
    md = ("\n\n" + SPLIT_MARK + "\n\n").join(
        "``````lean\n" + c.rstrip("\n") + "\n``````" for c in chunks) + "\n"
    r = subprocess.run(
        ["pandoc", "--from=gfm", "--to=latex", f"--syntax-definition={SYNTAX}"],
        input=md, capture_output=True, text=True, check=True, timeout=300)
    out = [part.strip() for part in SPLIT_RE.split(r.stdout)]
    if len(out) != len(chunks):
        raise RuntimeError(
            f"pandoc returned {len(out)} listings for {len(chunks)} chunks")
    return out


def margin(note: str) -> str:
    # Semantic, not typographic: each target decides what a gloss is. The
    # article preamble makes it a \marginpar, which LaTeXML renders as a note
    # and tuftify lifts into the Tufte margin; the book preamble sets it inline,
    # because that layout has no margin column and 2,891 floating marginpars
    # would fight the page on every spread.
    return "\\apmgloss{" + note + "}"


def local_uses(chunk: dict, known: list[str]) -> list[str]:
    """Earlier declarations in this file that this one names. Exact, not
    inferred: a token match against names the file itself declares."""
    body = "\n".join(chunk["lines"])
    seen, out = set(), []
    for tok in IDENT.findall(body):
        if tok in known and tok != chunk["name"] and tok not in seen:
            seen.add(tok)
            out.append(tok)
    return out


def render(pid: str, lean: Path, annotations: dict, informal: Path | None) -> str:
    text = lean.read_text()
    lines = text.split("\n")
    chunks = segment(lines)
    names = [c["name"] for c in chunks if c["name"]]

    parts = []
    head = []
    if informal and informal.is_file():
        m = CROSSREFS.search(informal.read_text())
        if m:
            refs = latex_escape(re.sub(r"[`*]", "", m.group(1)).strip().rstrip("."))
            head.append("The informal proof names these Mathlib results: " + refs + ".")
    n_sorry = len(SORRY.findall(re.sub(r"/-.*?-/", "", text, flags=re.S)))
    head.append(f"{len(names)} declaration{'s' if len(names) != 1 else ''}, "
                + ("no \\texttt{sorry}." if not n_sorry
                   else f"{n_sorry} \\texttt{{sorry}} remaining."))
    parts.append(margin(" ".join(head)))

    live = [(c, "\n".join(c["lines"]).strip("\n")) for c in chunks]
    live = [(c, code) for c, code in live if code.strip()]
    if not live:
        return ""
    listings = code_to_latex([code for _, code in live])

    for (chunk, _), listing in zip(live, listings):
        note = []
        if chunk["name"]:
            key = f"{pid}/{chunk['name']}"
            if key in annotations:
                note.append(annotations[key])
            uses = local_uses(chunk, names)
            if uses:
                shown = uses[:6]
                more = "" if len(uses) == len(shown) else f", and {len(uses) - len(shown)} more"
                note.append("Reuses " + ", ".join(
                    "\\texttt{" + latex_escape(u) + "}" for u in shown) + more + ".")
        if note:
            parts.append(margin(" ".join(note)))
        parts.append(listing)

    return "\n\n".join(parts) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("id_list")
    ap.add_argument("out_dir")
    ap.add_argument("--problems", default=str(REPO_ROOT / "problems"))
    args = ap.parse_args()

    if not SYNTAX.is_file():
        print(f"missing syntax definition: {SYNTAX}", file=sys.stderr)
        return 1
    annotations = json.loads(ANNOTATIONS.read_text()) if ANNOTATIONS.is_file() else {}

    problems = Path(args.problems)
    out_dir = Path(args.out_dir) / "lean"
    out_dir.mkdir(parents=True, exist_ok=True)
    ids = [x.strip() for x in Path(args.id_list).read_text().split() if x.strip()]

    written = skipped = 0
    for pid in ids:
        lean = problems / pid / "lean" / "Main.lean"
        if not lean.is_file():
            skipped += 1
            continue
        informal = problems / pid / "informal-solution.md"
        (out_dir / f"apm-{pid}.tex").write_text(
            render(pid, lean, annotations, informal))
        written += 1

    print(f"Rendered {written} Lean proof(s) -> {out_dir}/apm-*.tex"
          f" ({skipped} problem(s) have none"
          f"{'' if annotations else '; report/lean-annotations.json not present'})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
