#!/usr/bin/env python3
"""Project an APM problem's Arxana graph to a two-column LaTeX cheatsheet.

Reads entities and relations from futon1a (XTDB) via HTTP, assembles
the exposition (left column) and discipline annotations (right column)
with cross-references to ArSE questions and PlanetMath definitions.

Usage:
    python3 project-cheatsheet.py apm-t01A01
    python3 project-cheatsheet.py apm-t01A01 --open   # compile and open PDF
"""

import sys
import os
import json
import subprocess
from pathlib import Path
from urllib.request import Request, urlopen

SCRIPT_DIR = Path(__file__).parent
FUTON1A_URL = os.environ.get("FUTON1A_URL", "http://127.0.0.1:7071/api/alpha")
PENHOLDER = "api"
OUTPUT_DIR = Path.home() / "code" / "storage" / "canary"

# --- XTDB API helpers ---

def api_get(path):
    req = Request(f"{FUTON1A_URL}{path}", headers={"X-Penholder": PENHOLDER})
    with urlopen(req) as resp:
        # Response may be EDN, try to parse simply
        raw = resp.read().decode()
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return {"raw": raw}


def get_ego(name):
    """Get ego-centric view of an entity by name."""
    req = Request(f"{FUTON1A_URL}/ego/{name}", headers={"X-Penholder": PENHOLDER})
    with urlopen(req) as resp:
        raw = resp.read().decode()
        # EDN response — parse minimally
        return raw


def get_entity(name):
    """Get entity by name via /entity/:name endpoint."""
    req = Request(f"{FUTON1A_URL}/entity/{name}", headers={"X-Penholder": PENHOLDER})
    try:
        with urlopen(req) as resp:
            raw = resp.read().decode()
            try:
                return json.loads(raw)
            except json.JSONDecodeError:
                return {"raw": raw}
    except Exception:
        return None


# --- Minimal EDN parser for ego responses ---
# (Just enough to extract what we need)

import re

def parse_ego_relations(ego_raw):
    """Extract outgoing relations from ego EDN response.

    EDN format uses :keyword syntax, not quoted strings:
      {:relation {:type :has-phase}, :entity {:name "apm-t01A01-observe", ...}}
    """
    relations = []
    # Split on {:relation markers within :outgoing
    blocks = re.split(r'\{:relation\s+', ego_raw)
    for block in blocks[1:]:  # skip preamble
        # Type is an EDN keyword: :type :has-phase or :type :uses-definition
        type_m = re.search(r':type\s+:([a-z][\w/-]*)', block)
        # Name is a quoted string: :name "apm-t01A01-observe"
        name_m = re.search(r':name\s+"([^"]+)"', block)
        if type_m and name_m:
            relations.append({"type": type_m.group(1), "name": name_m.group(1)})
    return relations


def parse_entity_payload(entity_raw):
    """Extract payload fields from entity EDN response."""
    payload = {}
    if isinstance(entity_raw, dict) and "raw" in entity_raw:
        raw = entity_raw["raw"]
    elif isinstance(entity_raw, dict):
        return entity_raw.get("payload", entity_raw)
    else:
        raw = str(entity_raw)
    # Extract key-value pairs from payload
    for m in re.finditer(r'"(\w[\w-]*?)"\s*[.:]\s*"([^"]*)"', raw):
        payload[m.group(1)] = m.group(2)
    return payload


# --- Phase ordering ---

PHASE_ORDER = ["observe", "propose", "execute", "validate", "classify", "integrate"]
PHASE_LABELS = {
    "observe": "What's really being asked",
    "propose": "The key insight",
    "execute": "The proof",
    "validate": "Why it works",
    "classify": "Why it's interesting",
    "integrate": "Connections",
}
DISCIPLINE_LABELS = {
    "observe": "SPEC / Framing-first",
    "propose": "CONSTRUCT / QP-7 Kernel",
    "execute": "CONSTRUCT / Compose Lemmas",
    "validate": "VERIFY / Non-circularity",
    "classify": "VERIFY / QP-8 Confidence",
    "integrate": "MAP / QP-1 Landscape",
}


def escape_latex(s):
    """Escape special LaTeX characters, preserving $..$ math.

    Uses futon6's normalize-math-prose.py for heavy lifting if available,
    falls back to conservative escaping.
    """
    # Strip literal \n sequences (from EDN string escaping)
    s = s.replace('\\n', ' ')

    # Use futon6's normalize-math-prose.py for prose → math conversion
    try:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "normalize_math_prose",
            Path.home() / "code" / "futon6" / "scripts" / "normalize-math-prose.py",
        )
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        s = mod.process_line(s)
    except Exception:
        pass  # fall through to manual escaping below

    # Escape remaining non-math chars
    # If the text already contains $\cmd$ patterns, it's LaTeX-ready
    # and we should NOT escape braces (they're intentional)
    has_latex_math = bool(re.search(r'\$\\', s))

    parts = re.split(r'(\$[^$]+\$)', s)
    result = []
    for part in parts:
        if part.startswith('$') and part.endswith('$'):
            result.append(part)
        else:
            if not has_latex_math:
                part = part.replace('{', r'\{')
                part = part.replace('}', r'\}')
            part = part.replace('&', r'\&')
            part = part.replace('%', r'\%')
            part = part.replace('#', r'\#')
            # Only escape _ and ^ that survived the normalizer
            part = part.replace('_', r'\_')
            part = part.replace('^', r'\^{}')
            part = part.replace('--', '---')
            # Hyperlink theorem names
            THEOREM_URLS = {
                "Closed Graph Theorem": "https://en.wikipedia.org/wiki/Closed_graph_theorem",
                "Hellinger-Toeplitz": "https://en.wikipedia.org/wiki/Hellinger%E2%80%93Toeplitz_theorem",
                "Hellinger---Toeplitz": "https://en.wikipedia.org/wiki/Hellinger%E2%80%93Toeplitz_theorem",
                "Brouwer": "https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem",
                "Borsuk-Ulam": "https://en.wikipedia.org/wiki/Borsuk%E2%80%93Ulam_theorem",
                "Borsuk---Ulam": "https://en.wikipedia.org/wiki/Borsuk%E2%80%93Ulam_theorem",
                "Fatou": "https://en.wikipedia.org/wiki/Fatou%27s_lemma",
                "Dominated Convergence": "https://en.wikipedia.org/wiki/Dominated_convergence_theorem",
                "DCT": "https://en.wikipedia.org/wiki/Dominated_convergence_theorem",
                "Cauchy-Schwarz": "https://en.wikipedia.org/wiki/Cauchy%E2%80%93Schwarz_inequality",
                "Cauchy---Schwarz": "https://en.wikipedia.org/wiki/Cauchy%E2%80%93Schwarz_inequality",
                "Banach-Alaoglu": "https://en.wikipedia.org/wiki/Banach%E2%80%93Alaoglu_theorem",
                "Gauss lemma": "https://en.wikipedia.org/wiki/Gauss%27s_lemma_(polynomial)",
            }
            for name, url in THEOREM_URLS.items():
                if name in part:
                    part = part.replace(name, rf"\href{{{url}}}{{{name}}}")
            result.append(part)
    return ''.join(result)


def load_proof_cycles(problem_name):
    """Load all proof cycles from proof state EDN on disk.

    Returns a list of cycle dicts, each with:
      - blocker: the ledger item this cycle targets
      - notes: {phase: note_text} for phases that have notes
      - status: cycle result status

    For multi-part problems (b03J02, m96A04), this returns one cycle
    per sub-part plus a root cycle, in the order they appear in the
    proof state.
    """
    state_path = Path.home() / "code" / "futon3c" / "data" / "proof-state" / f"{problem_name}.edn"
    if not state_path.exists():
        return [], []

    text = state_path.read_text()

    def unescape_edn_string(s):
        if s is None:
            return ""
        s = s.replace('\\\\', '\\')
        return ' '.join(s.split())

    # Split into cycle blocks by finding either the old :cycle/id shape
    # or the current namespaced-map shape #:cycle{:id "..."}.
    cycle_starts = [m.start() for m in re.finditer(r'(?::cycle/id|#:cycle\{:id)\s+"', text)]
    cycles = []

    for i, start in enumerate(cycle_starts):
        end = cycle_starts[i + 1] if i + 1 < len(cycle_starts) else len(text)
        block = text[start:end]

        # Extract cycle metadata
        cid_m = re.search(r'(?::cycle/id|#:cycle\{:id)\s+"([^"]+)"', block)
        blocker_m = re.search(r'(?::cycle/blocker-id|:blocker-id)\s+"([^"]+)"', block)
        status_m = re.search(r'(?::cycle/result-status|:result-status)\s+:(\w+)', block)

        if not cid_m:
            continue

        cycle = {
            "id": cid_m.group(1),
            "blocker": blocker_m.group(1) if blocker_m else "root",
            "status": status_m.group(1) if status_m else "unknown",
            "notes": {},
        }

        # Extract phase notes from this cycle's block
        for phase in PHASE_ORDER:
            pattern = rf':{phase}\s+\{{.*?:notes\s+"((?:\\.|[^"])*)"'
            m = re.search(pattern, block)
            if m:
                cycle["notes"][phase] = unescape_edn_string(m.group(1))

        # Only include cycles that have at least one note
        if cycle["notes"]:
            cycles.append(cycle)

    # Keep only the LAST cycle per blocker (most recent = best notes)
    seen_blockers = {}
    for c in cycles:
        seen_blockers[c["blocker"]] = c
    cycles = list(seen_blockers.values())

    # Extract failed routes (global, not per-cycle)
    failed_routes = []
    for m in re.finditer(r':route/approach\s+"([^"]*)"', text):
        approach = m.group(1)
        obs_m = re.search(r':route/structural-obstruction\s+"([^"]*)"', text[m.start():])
        obstruction = obs_m.group(1) if obs_m else ""
        fr = {"approach": approach, "obstruction": obstruction}
        fr["approach"] = unescape_edn_string(fr["approach"])
        fr["obstruction"] = unescape_edn_string(fr["obstruction"])
        failed_routes.append(fr)

    return cycles, failed_routes


def load_pm_coverage(problem_name):
    """Load PlanetMath term coverage from canary report."""
    base = problem_name.replace("apm-", "")
    report_path = OUTPUT_DIR / f"{base}-planetmath.edn"
    if not report_path.exists():
        return []

    text = report_path.read_text()
    terms = []
    for m in re.finditer(r':term\s+"([^"]*)"', text):
        terms.append({"term": m.group(1)})
    return terms


def load_arse_questions(problem_name):
    """Load ArSE questions from canary report."""
    base = problem_name.replace("apm-", "")
    report_path = OUTPUT_DIR / f"{base}-arse.edn"
    # Map question types to phases
    type_to_phase = {
        "why-hard": "observe",
        "what-crux": "propose",
        "why-works": "validate",
        "what-connects": "integrate",
        "confidence": "classify",
    }
    questions = []

    if report_path.exists():
        text = report_path.read_text()
        for m in re.finditer(r':type\s+"([^"]*)".*?:thread-id\s+"([^"]*)"', text):
            qtype, tid = m.group(1), m.group(2)
            questions.append({
                "type": qtype,
                "thread-id": tid,
                "phase": type_to_phase.get(qtype, ""),
                "title": {"why-hard": "Why is this hard?",
                           "what-crux": "What is the key insight?",
                           "why-works": "Why does this proof work?",
                           "what-connects": "What does this connect to?",
                           "confidence": "What is surprising here?"}.get(qtype, qtype),
            })
        if questions:
            return questions

    # Fallback: read inline ArSE questions from the persisted proof-state.
    state_path = Path.home() / "code" / "futon3c" / "data" / "proof-state" / f"{problem_name}.edn"
    if not state_path.exists():
        return []

    text = state_path.read_text()
    for m in re.finditer(r':type\s+:([a-z-]+),\s+:question\s+"((?:\\.|[^"])*)",\s+:answer\s+"((?:\\.|[^"])*)"', text):
        qtype, question, _answer = m.groups()
        questions.append({
            "type": qtype,
            "thread-id": "",
            "phase": type_to_phase.get(qtype, ""),
            "title": question.replace('\\\\', '\\'),
        })
    return questions


def build_cheatsheet(problem_name):
    """Build two-column LaTeX cheatsheet from Arxana graph + local state."""

    # Graph structure from XTDB (what's connected to what)
    ego_raw = get_ego(problem_name)
    relations = parse_ego_relations(ego_raw)

    # All proof cycles from proof state (may be multiple for sub-parts)
    cycles, failed_routes = load_proof_cycles(problem_name)

    # PlanetMath terms from coverage report
    pm_terms = load_pm_coverage(problem_name)

    # ArSE questions from canary report
    arse_questions = load_arse_questions(problem_name)

    # For single-cycle problems, keep the old behaviour
    # For multi-cycle, we'll render each cycle as a section
    is_multipart = len(cycles) > 1

    # Extract problem metadata from name
    base = problem_name.replace("apm-", "")
    subject_map = {"a": "Analysis", "b": "Algebra", "m": "Functional Analysis", "t": "Topology"}
    subject = subject_map.get(base[0], "Unknown")

    m = re.match(r"[a-z](\d{2})([AJ])(\d+)", base)
    if m:
        year = 2000 + int(m.group(1)) if int(m.group(1)) < 80 else 1900 + int(m.group(1))
        session = "Spring" if m.group(2) == "A" else "Fall"
        number = m.group(3)
    else:
        year, session, number = "?", "?", "?"

    # --- Render LaTeX ---
    tex = []
    tex.append(r"""\documentclass[11pt]{article}
\usepackage[a4paper,landscape,margin=1.5cm,top=1.2cm,bottom=1.2cm]{geometry}
\usepackage{fontspec}
\usepackage{setspace}
\usepackage{xcolor}
\usepackage{paracol}
\usepackage{parskip}
\usepackage{amsmath,amssymb}

\setmainfont{TeX Gyre Termes}
\newfontfamily\tagfont{TeX Gyre Heros}

\definecolor{warrant}{RGB}{100,60,20}
\definecolor{phase}{RGB}{30,60,100}
\definecolor{pattag}{RGB}{120,30,30}
\definecolor{graynote}{gray}{0.40}
\definecolor{lncolor}{gray}{0.45}
\definecolor{arseblue}{RGB}{40,80,140}
\definecolor{pmgreen}{RGB}{30,100,50}

\usepackage[colorlinks=true,linkcolor=phase,urlcolor=pmgreen,citecolor=arseblue]{hyperref}

\newcommand{\lno}[1]{{\tagfont\footnotesize\textcolor{lncolor}{#1}\enspace}}
\newcommand{\phaselabel}[1]{%
  \par\medskip\noindent{\tagfont\small\textcolor{phase}{\textsc{#1}}}\\*%
}
\newcommand{\discheader}[2]{%
  \noindent{\tagfont\footnotesize\textcolor{pattag}{\textbf{#1}}\enspace%
  \textcolor{phase}{\textit{#2}}}\par\vspace{2pt}%
}
\newcommand{\arseref}[2]{%
  {\tagfont\scriptsize\textcolor{arseblue}{$\triangleright$ #1: #2}}\par\vspace{2pt}%
}
\newcommand{\pmterm}[2]{{\tagfont\tiny\href{#2}{\textcolor{pmgreen}{#1}}}}

% APM exam macros (from the UT Austin prelim archive)
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
\newcommand{\ie}{i.e.}
\newcommand{\pipe}{\mid}
\newcommand{\soln}[1]{}
\newenvironment{alist}{\begin{enumerate}[(a)]}{\end{enumerate}}
\usepackage{enumerate}

\pagestyle{empty}
\begin{document}
""")

    tex.append(r"\begin{center}")
    tex.append(rf"{{\LARGE\textbf{{APM Cheatsheet — {escape_latex(base)}}}}}")
    tex.append(r"\medskip")
    tex.append(rf"{{\tagfont {subject}, {session} {year}, Problem {number}}}")
    tex.append(r"\end{center}")
    tex.append(r"\medskip")

    # Problem statement in abstract-like environment
    problem_tex = SCRIPT_DIR / f"{base}.tex"
    if problem_tex.exists():
        raw_statement = problem_tex.read_text().strip()
        # Clean up comment lines (%%% separators, %--- lines)
        lines = [l for l in raw_statement.split('\n')
                 if not l.strip().startswith('%')]
        clean_statement = '\n'.join(lines).strip()
        tex.append(r"\begin{quote}")
        tex.append(r"\small\textbf{Problem.} " + clean_statement)
        tex.append(r"\end{quote}")
    tex.append(r"\smallskip")

    # PM terms are now in column 3 (removed from header)

    # Three-column body: exposition | discipline | meta (ArSE + connections)
    tex.append(r"\columnratio{0.45,0.30,0.25}")
    tex.append(r"\begin{paracol}{3}")
    tex.append(r"\setstretch{1.15}")

    lno = 1
    total_phases = 0
    phase_index = []  # tracks {lno, phase, cycle_blocker} for cross-refs

    # Pretty labels for sub-parts
    PART_LABELS = {
        "part-a": "Part (a)", "part-b": "Part (b)", "part-c": "Part (c)",
        "part-d": "Part (d)", "root": "Synthesis",
    }

    for cycle in cycles:
        blocker = cycle["blocker"]
        notes = cycle["notes"]

        if not notes:
            continue

        # Section header for multi-part problems
        if is_multipart:
            part_label = PART_LABELS.get(blocker, blocker)
            if lno > 1:  # not the first section
                tex.append(r"\medskip\noindent\rule{\linewidth}{0.4pt}\medskip")
            tex.append(rf"\noindent{{\tagfont\large\textbf{{{part_label}}}}}\par\smallskip")

        # Left column: exposition phases
        # Build index for cross-referencing: each phase gets lno, letter
        for phase_name in PHASE_ORDER:
            note = notes.get(phase_name, "")
            if not note:
                continue

            label = PHASE_LABELS.get(phase_name, phase_name)
            tex.append(rf"\phaselabel{{{label}}}")
            tex.append(rf"\lno{{{lno}}} {escape_latex(note)}")
            tex.append(r"\smallskip")

            # Track for cross-referencing
            phase_index.append({
                "lno": lno,
                "phase": phase_name,
                "cycle_blocker": blocker,
            })

            lno += 1
            total_phases += 1

    # Failed routes (after all cycles)
    if failed_routes:
        tex.append(r"\phaselabel{Dead end}")
        for fr in failed_routes:
            approach = fr.get("approach", "?")
            obstruction = fr.get("obstruction", fr.get("structural-obstruction", "?"))
            tex.append(rf"\lno{{{lno}}} \textit{{Naive attempt:}} {escape_latex(approach)}")
            tex.append(r"\par\smallskip")
            tex.append(rf"\hspace{{1em}}\textit{{Why it fails:}} {escape_latex(obstruction)}")
            tex.append(r"\smallskip")
            lno += 1

    # Column 2: Discipline warrants — pattern tag + short insight
    # Source: ArSE *answers* (they capture the discipline voice)
    # Falls back to first sentence of phase notes if no ArSE answer
    tex.append(r"\switchcolumn")
    tex.append(r"\setstretch{1.05}")

    # Build ArSE answer lookup: phase → answer text
    arse_answers = {}
    type_to_phase = {
        "why-hard": "observe", "what-crux": "propose",
        "why-works": "validate", "what-connects": "integrate",
        "confidence": "classify",
    }
    # Load answers from evidence store canary reports
    arse_report_path = OUTPUT_DIR / f"{base}-arse.edn"
    # For now, use the phase notes' first sentence as the warrant
    # (ArSE answers are the same text; the value is the separation)

    for pi in phase_index:
        n = pi["lno"]
        disc_label = DISCIPLINE_LABELS.get(pi["phase"], pi["phase"])
        ref = f"{n}.A"

        # Get the full note, extract first sentence as warrant
        warrant = ""
        for cycle in cycles:
            note = cycle["notes"].get(pi["phase"], "")
            if note and cycle["blocker"] == pi["cycle_blocker"]:
                # First sentence: up to first '. ' or whole thing if short
                sentences = re.split(r'(?<=[.!?])\s+', note)
                warrant = escape_latex(sentences[0]) if sentences else ""
                break

        tex.append(r"\par\vspace{3pt}")
        tex.append(rf"\noindent{{\tagfont\footnotesize\textcolor{{lncolor}}{{{ref}}}\enspace\textcolor{{pattag}}{{\textbf{{{disc_label}}}}}\enspace\color{{warrant}}{warrant}}}")

    # Column 3: Questions & References with cross-reference numbers
    tex.append(r"\switchcolumn")
    tex.append(r"\setstretch{1.05}")

    # PlanetMath definitions reference the problem (0.a, 0.b, ...)
    if pm_terms:
        for ti, t in enumerate(pm_terms[:10]):
            term = t.get("term", "?")
            canon = t.get("canon", term)
            url = f"https://planetmath.org/entry/{canon}"
            letter = chr(ord('a') + ti)
            tex.append(rf"\par\vspace{{3pt}}\noindent{{\tagfont\footnotesize\textcolor{{lncolor}}{{0.{letter}}}\enspace\href{{{url}}}{{\textcolor{{pmgreen}}{{{escape_latex(term)}}}}}}}")
        tex.append(r"\medskip")

    # ArSE questions — the *questions themselves* show what thinking is needed
    if arse_questions:
        for aq in arse_questions:
            title = aq.get("title", "?")
            tid = aq.get("thread-id", "?")
            qphase = aq.get("phase", type_to_phase.get(aq.get("type", ""), ""))

            parent_lno = "?"
            for pi in phase_index:
                if pi["phase"] == qphase:
                    parent_lno = pi["lno"]
                    break

            ref = f"{parent_lno}.A.a"
            tex.append(r"\par\vspace{3pt}")
            tex.append(rf"\noindent{{\tagfont\footnotesize\textcolor{{lncolor}}{{{ref}}}\enspace\textcolor{{arseblue}}{{{escape_latex(title)}}}\enspace\textcolor{{graynote}}{{{tid}}}}}")

    tex.append(r"\end{paracol}")

    # Footer
    tex.append(r"\bigskip")
    tex.append(r"\begin{center}")
    tex.append(r"{\tagfont\small\textcolor{graynote}{%")
    tex.append(r"  Projected from Arxana $\cdot$ futon1a/XTDB $\cdot$")
    tex.append(rf"  {len(cycles)} cycles $\cdot$ {total_phases} phases $\cdot$ {len(arse_questions)} ArSE questions $\cdot$ {len(pm_terms)} PM terms}}}}")
    tex.append(r"\end{center}")
    tex.append(r"\end{document}")

    return "\n".join(tex)


def main():
    args = sys.argv[1:]
    do_open = "--open" in args
    args = [a for a in args if a != "--open"]

    if not args:
        print(__doc__)
        sys.exit(1)

    problem_name = args[0]
    tex = build_cheatsheet(problem_name)

    # Write TeX file
    out_path = OUTPUT_DIR / f"{problem_name.replace('apm-', '')}.tex"
    out_path.write_text(tex)
    print(f"TeX written to {out_path}")

    if do_open:
        # Compile with lualatex
        result = subprocess.run(
            ["lualatex", "-interaction=nonstopmode", str(out_path)],
            cwd=str(OUTPUT_DIR),
            capture_output=True,
            timeout=30,
        )
        pdf_path = out_path.with_suffix(".pdf")
        if pdf_path.exists():
            print(f"PDF: {pdf_path}")
            subprocess.Popen(["xdg-open", str(pdf_path)])
        else:
            print(f"Compilation failed: {result.stderr.decode()[-200:]}")


if __name__ == "__main__":
    main()
