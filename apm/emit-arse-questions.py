#!/usr/bin/env python3
"""Emit ArSE pedagogical questions from a completed proof cycle.

Reads phase-data notes from a proof state file and emits 5 question/answer
pairs via the ArSE HTTP API, tagged with namespace and question type.

Usage:
    python3 emit-arse-questions.py apm-t01A01
    python3 emit-arse-questions.py apm-b03J02 --cycle apm-b03J02-C001
    python3 emit-arse-questions.py --canary
"""

import sys
import json
import re
import os
from pathlib import Path
from urllib.request import Request, urlopen
from urllib.error import URLError

# --- Config ---
FUTON3C_URL = os.environ.get("FUTON3C_URL", "http://127.0.0.1:47070")
ADMIN_TOKEN = None  # loaded lazily
PROOF_STATE_DIR = Path.home() / "code" / "futon3c" / "data" / "proof-state"
CANARY_DIR = Path.home() / "code" / "storage" / "canary"

CANARY_IDS = ["apm-t01A01", "apm-b03J02"]  # only ones with completed cycles

# --- Subject from problem ID ---
SUBJECT_MAP = {"a": "analysis", "b": "algebra", "m": "applied", "t": "topology"}

MANIFEST = None


def load_manifest():
    global MANIFEST
    if MANIFEST is None:
        manifest_path = Path.home() / "code" / "storage" / "apm" / "manifest.edn"
        # Simple EDN parsing for our manifest: extract id, subject, year, number
        MANIFEST = {}
        text = manifest_path.read_text()
        for m in re.finditer(r':id "([^"]+)"', text):
            MANIFEST[m.group(1)] = True  # just need existence
    return MANIFEST


def problem_tags(problem_id):
    """Generate namespace tags from problem ID like apm-t01A01."""
    base = problem_id.replace("apm-", "")
    prefix = base[0]
    subject = SUBJECT_MAP.get(prefix, "unknown")

    # Parse year/number from filename pattern
    m = re.match(r"[a-z](\d{2})([AJ])(\d+)", base)
    if m:
        year_2d = int(m.group(1))
        year = 2000 + year_2d if year_2d < 80 else 1900 + year_2d
        number = m.group(3)
        return [
            "apm",
            f"apm/{subject}",
            f"apm/{subject}/{year}",
            f"apm/{subject}/{year}/{number}",
        ]
    return ["apm", f"apm/{subject}"]


def load_admin_token():
    global ADMIN_TOKEN
    if ADMIN_TOKEN is None:
        token_path = Path.home() / "code" / "futon3c" / ".admintoken"
        ADMIN_TOKEN = token_path.read_text().strip()
    return ADMIN_TOKEN


def arse_ask(title, question, tags, author="claude"):
    """Post a question to ArSE via HTTP API."""
    payload = json.dumps({
        "title": title,
        "question": question,
        "tags": tags,
        "author": author,
    }).encode()

    req = Request(
        f"{FUTON3C_URL}/api/alpha/arse/ask",
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )

    try:
        with urlopen(req) as resp:
            result = json.loads(resp.read())
            return result
    except URLError as e:
        return {"ok": False, "error": str(e)}


def arse_answer(thread_id, answer, author="claude"):
    """Post an answer to ArSE via HTTP API."""
    payload = json.dumps({
        "thread-id": thread_id,
        "answer": answer,
        "author": author,
    }).encode()

    req = Request(
        f"{FUTON3C_URL}/api/alpha/arse/answer",
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )

    try:
        with urlopen(req) as resp:
            return json.loads(resp.read())
    except URLError as e:
        return {"ok": False, "error": str(e)}


# --- Question taxonomy ---
# Maps proof phase → question type → question template

QUESTION_TYPES = [
    {
        "type": "why-hard",
        "phase": "observe",
        "template": "Why is this problem hard? What trap does it set?",
    },
    {
        "type": "what-crux",
        "phase": "propose",
        "template": "What is the key insight needed to solve this?",
    },
    {
        "type": "why-works",
        "phase": "validate",
        "template": "Why does this proof work? What are the key hypotheses?",
    },
    {
        "type": "what-connects",
        "phase": "integrate",
        "template": "What broader themes does this connect to?",
    },
    {
        "type": "confidence",
        "phase": "classify",
        "template": "What is surprising or counterintuitive here?",
    },
]


def extract_phase_notes(proof_state, cycle_id=None):
    """Extract phase-data notes from a completed cycle."""
    cycles = proof_state.get("proof/cycles", [])
    if not cycles:
        return {}

    # Find the target cycle
    cycle = None
    if cycle_id:
        for c in cycles:
            if c.get("cycle/id") == cycle_id:
                cycle = c
                break
    else:
        # Use the last completed cycle
        for c in reversed(cycles):
            if c.get("cycle/phase") == "completed":
                cycle = c
                break
        if cycle is None:
            cycle = cycles[-1]  # fallback to last

    phase_data = cycle.get("cycle/phase-data", {})
    notes = {}
    for phase_key, data in phase_data.items():
        if isinstance(data, dict) and "notes" in data:
            # phase_key might be a keyword like :observe or string "observe"
            phase_name = str(phase_key).lstrip(":")
            notes[phase_name] = data["notes"]

    return notes


def load_proof_state_edn(problem_id):
    """Load proof state from EDN file. Simple regex-based extraction."""
    path = PROOF_STATE_DIR / f"{problem_id}.edn"
    if not path.exists():
        return None

    text = path.read_text()

    # Extract cycles with phase-data containing notes
    # This is a simplified parser for the specific shape we produce
    state = {"proof/cycles": []}

    # Find cycle blocks
    cycle_pattern = r':cycle/id\s+"([^"]+)"'
    cycle_ids = re.findall(cycle_pattern, text)

    # For each cycle, find phase-data notes
    for cid in cycle_ids:
        cycle = {"cycle/id": cid, "cycle/phase-data": {}, "cycle/phase": "completed"}

        # Find notes for each phase within this cycle's context
        # Look for patterns like :observe {:blocker-id "root" :notes "..."}
        for phase in ["observe", "propose", "execute", "validate", "classify", "integrate"]:
            # Find :phase {... :notes "..."}
            pattern = rf':{phase}\s+\{{[^}}]*:notes\s+"([^"]*)"'
            m = re.search(pattern, text)
            if m:
                cycle["cycle/phase-data"][phase] = {"notes": m.group(1)}

        state["proof/cycles"].append(cycle)

    return state


def emit_questions(problem_id, cycle_id=None):
    """Emit 5 pedagogical questions for a problem."""
    state = load_proof_state_edn(problem_id)
    if state is None:
        print(f"  SKIP {problem_id}: no proof state found")
        return []

    notes = extract_phase_notes(state, cycle_id)
    if not notes:
        print(f"  SKIP {problem_id}: no phase notes found")
        return []

    tags = problem_tags(problem_id)
    base_id = problem_id.replace("apm-", "")
    results = []

    for qt in QUESTION_TYPES:
        phase_note = notes.get(qt["phase"], "")
        if not phase_note:
            continue

        # Question title includes problem ID and type
        title = f"[{base_id}] {qt['template']}"
        question = f"Problem {base_id}: {qt['template']}"
        answer = phase_note

        q_tags = tags + [qt["type"]]

        # Ask
        q_result = arse_ask(title, question, q_tags)
        if not q_result.get("ok"):
            print(f"  FAIL ask {qt['type']}: {q_result}")
            continue

        thread_id = q_result.get("thread-id", "")

        # Answer
        a_result = arse_answer(thread_id, answer)
        if not a_result.get("ok"):
            print(f"  FAIL answer {qt['type']}: {a_result}")

        results.append({
            "type": qt["type"],
            "phase": qt["phase"],
            "thread_id": thread_id,
            "question": question,
            "answer_preview": phase_note[:80] + "..." if len(phase_note) > 80 else phase_note,
        })

        print(f"    {qt['type']:15s} → {thread_id}")

    return results


def main():
    args = sys.argv[1:]

    if "--canary" in args:
        problem_ids = CANARY_IDS
    elif args:
        problem_ids = [a for a in args if not a.startswith("--")]
    else:
        print(__doc__)
        sys.exit(1)

    cycle_id = None
    for i, a in enumerate(args):
        if a == "--cycle" and i + 1 < len(args):
            cycle_id = args[i + 1]

    for pid in problem_ids:
        print(f"  {pid}:")
        results = emit_questions(pid, cycle_id)

        # Write report for canary
        report_path = CANARY_DIR / f"{pid.replace('apm-', '')}-arse.edn"
        with open(report_path, "w") as f:
            f.write(f";; ArSE questions for {pid}\n")
            f.write("{\n")
            f.write(f' :id "{pid}"\n')
            f.write(f" :questions-emitted {len(results)}\n")
            f.write(" :questions [\n")
            for r in results:
                tid = r["thread_id"]
                qtype = r["type"]
                f.write(f'   {{:type "{qtype}" :thread-id "{tid}"}}\n')
            f.write(" ]\n}\n")

        if results:
            print(f"    → {len(results)} questions emitted")
        print()


if __name__ == "__main__":
    main()
