#!/usr/bin/env python3
"""Ratchet validator for APM cheatsheet TeX output.

Checks invariants on generated .tex files BEFORE compilation.
If any check fails, the cheatsheet is rejected with a diagnostic.

Usage:
    python3 check-cheatsheet.py canary/t01A01.tex
    python3 check-cheatsheet.py canary/*.tex

Invariants enforced:
  T1: No bare _ outside $...$ (subscript leak)
  T2: No bare ^ outside $...$ (superscript leak)
  T3: No bare < or > outside $...$ (angle bracket leak)
  T4: No \_ or \^{} (escaped math markers = prose math leak)
  T5: No bare Greek letter names outside $...$ (alpha, beta, pi, etc.)
  T6: Balanced $ delimiters per line (odd count = unclosed math)
  T7: LaTeX compiles without errors
"""

import re
import sys
import subprocess
from pathlib import Path

# Lines to skip: preamble, macro definitions, raw problem statement
SKIP_PATTERNS = [
    re.compile(r"^\\(?!lno)"),    # LaTeX commands at start of line (but NOT \lno content)
    re.compile(r"^\s*$"),         # blank lines
    re.compile(r"^%"),            # comments
    re.compile(r"\\begin\{"),     # environments
    re.compile(r"\\end\{"),
    re.compile(r"\\newcommand"),
    re.compile(r"\\renewcommand"),
    re.compile(r"\\definecolor"),
    re.compile(r"\\usepackage"),
    re.compile(r"\\setmainfont"),
    re.compile(r"\\pagestyle"),
    re.compile(r"\\columnratio"),
    re.compile(r"\\setstretch"),
    re.compile(r"\\switchcolumn"),
    re.compile(r"\\small\\textbf\{Problem"),  # raw problem statement
]

# Greek letter names that should be in math mode
GREEK_NAMES = (
    "alpha|beta|gamma|delta|epsilon|zeta|eta|theta|iota|kappa|"
    "lambda|mu|nu|xi|pi|rho|sigma|tau|phi|chi|psi|omega"
)


def is_content_line(line):
    """Return True if this line contains prose/math content to check."""
    stripped = line.strip()
    if not stripped:
        return False
    for pat in SKIP_PATTERNS:
        if pat.match(stripped):
            return False
    return True


def extract_prose_segments(line):
    """Split line into math ($...$) and prose segments. Return prose only."""
    parts = re.split(r'(\$[^$]+\$)', line)
    prose = []
    for part in parts:
        if part.startswith('$') and part.endswith('$'):
            continue  # skip math
        prose.append(part)
    return prose


def check_file(path):
    """Run all invariant checks on a .tex file. Returns list of violations."""
    text = Path(path).read_text()
    lines = text.split('\n')
    violations = []

    # Track whether we're inside the problem statement quote
    in_problem_quote = False

    for lineno, line in enumerate(lines, 1):
        stripped = line.strip()

        # Track problem statement block (raw LaTeX, skip checks)
        if r'\small\textbf{Problem.}' in line:
            in_problem_quote = True
            continue
        if in_problem_quote and r'\end{quote}' in line:
            in_problem_quote = False
            continue
        if in_problem_quote:
            continue

        if not is_content_line(line):
            continue

        prose_segments = extract_prose_segments(line)
        prose_text = ' '.join(prose_segments)

        # T1: No bare _ outside math
        for seg in prose_segments:
            # Strip \href{...} URLs before checking (URLs contain _)
            seg_no_href = re.sub(r'\\href\{[^}]*\}', '', seg)
            bare_underscores = re.findall(r'(?<!\\)_', seg_no_href)
            if bare_underscores:
                violations.append({
                    "rule": "T1",
                    "line": lineno,
                    "message": f"Bare _ outside math mode",
                    "context": seg.strip()[:80],
                })

        # T2: No bare ^ outside math
        for seg in prose_segments:
            bare_carets = re.findall(r'(?<!\\)\^', seg)
            if bare_carets:
                violations.append({
                    "rule": "T2",
                    "line": lineno,
                    "message": f"Bare ^ outside math mode",
                    "context": seg.strip()[:80],
                })

        # T3: No bare < or > outside math (likely inner product leak)
        for seg in prose_segments:
            # Allow \< and \> (escaped), and HTML-like tags
            bare_angles = re.findall(r'(?<!\\)[<>]', seg)
            if bare_angles:
                violations.append({
                    "rule": "T3",
                    "line": lineno,
                    "message": f"Bare {'<' if '<' in bare_angles else '>'} outside math (inner product leak?)",
                    "context": seg.strip()[:80],
                })

        # T4: Escaped math markers (\_ or \^{}) = prose math leak
        for seg in prose_segments:
            if r'\_' in seg or r'\^{}' in seg:
                violations.append({
                    "rule": "T4",
                    "line": lineno,
                    "message": "Escaped math marker (\\_  or \\^{}) — should be in $...$",
                    "context": seg.strip()[:80],
                })

        # T5: Bare Greek letter names outside math
        for seg in prose_segments:
            greek_matches = re.findall(
                rf'\b({GREEK_NAMES})\b',
                seg, re.IGNORECASE,
            )
            # Filter out common English words that happen to be Greek
            false_positives = {"nu", "chi", "mu", "eta", "iota", "xi"}
            for gm in greek_matches:
                if gm.lower() not in false_positives:
                    violations.append({
                        "rule": "T5",
                        "line": lineno,
                        "message": f"Bare Greek '{gm}' outside math mode",
                        "context": seg.strip()[:80],
                    })

        # T6: Balanced $ per line (odd = unclosed math)
        dollar_count = line.count('$') - line.count(r'\$')
        if dollar_count % 2 != 0:
            violations.append({
                "rule": "T6",
                "line": lineno,
                "message": f"Odd number of $ ({dollar_count}) — unclosed math?",
                "context": stripped[:80],
            })

    return violations


def check_compiles(path):
    """Try to compile with lualatex. Return error lines if failure."""
    result = subprocess.run(
        ["lualatex", "-interaction=nonstopmode", "-halt-on-error", str(path)],
        capture_output=True,
        timeout=30,
        cwd=str(Path(path).parent),
    )
    if result.returncode != 0:
        stderr = result.stdout.decode(errors="replace")
        errors = [l for l in stderr.split('\n') if l.startswith('!')]
        return errors[:5]
    return []


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        sys.exit(1)

    total_violations = 0
    for path in args:
        p = Path(path)
        if not p.exists():
            print(f"  SKIP {path}: not found")
            continue

        violations = check_file(p)
        compile_errors = check_compiles(p)

        if compile_errors:
            violations.append({
                "rule": "T7",
                "line": 0,
                "message": "LaTeX compilation failed",
                "context": compile_errors[0] if compile_errors else "unknown",
            })

        if violations:
            print(f"  FAIL {p.name}: {len(violations)} violation(s)")
            for v in violations[:10]:
                print(f"    [{v['rule']}] L{v['line']}: {v['message']}")
                if v['context']:
                    print(f"           {v['context'][:60]}")
            total_violations += len(violations)
        else:
            print(f"  PASS {p.name}")

    if total_violations:
        print(f"\n  {total_violations} total violations")
        sys.exit(1)
    else:
        print(f"\n  All checks passed")
        sys.exit(0)


if __name__ == "__main__":
    main()
