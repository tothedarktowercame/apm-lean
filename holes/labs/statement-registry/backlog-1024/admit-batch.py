#!/usr/bin/env python3
"""Admit the faithful/stronger rows of one backlog grades file (2026-10-24).

Usage: admit-batch.py NN   (reads grades-NN.md; prints the non-admitted rows)
The registry's own admit refuses flagged statements (axiom, opaque, sorry, bare ⊤).
"""
import json, re, subprocess, sys
from pathlib import Path
D = Path(__file__).resolve().parent
ROOT = D.parents[3]
n = sys.argv[1]
grades = D / f"grades-{n}.md"
held = []
for line in grades.read_text().splitlines():
    m = re.match(r"\|\s*([A-Za-z0-9-]+)\s*\|\s*([a-z-]+)\s*\|(.*)", line)
    if not m or m.group(1) == "id" or set(m.group(1)) == {"-"}:
        continue
    pid, grade = m.group(1), m.group(2)
    reg = json.loads((ROOT / "problems/STATEMENTS.json").read_text())
    if pid in reg["entries"]:
        continue
    if any(r.get("id") == pid for r in reg.get("revoked", [])):
        held.append((pid, "revoked", "reviewer revoked the admission; see held.md"))
        continue
    if grade in ("faithful", "stronger"):
        cmd = [sys.executable, str(ROOT / "scripts/statement-registry.py"), "admit", pid,
               "--grade", grade, "--grader", f"codex read-only grader (backlog-1024 batch {n})",
               "--evidence", str(grades.relative_to(ROOT))]
        r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        if r.returncode and "no theorem apm_" in r.stderr:
            # Older canaries have no apm_<id>; the grader read the whole file,
            # so pin every top-level `theorem` (helpers are `lemma`).
            src = (ROOT / "problems" / pid / "lean/Main.lean").read_text()
            names = re.findall(r"^theorem\s+([^\s({\[:]+)", src, re.M)
            if names:
                r = subprocess.run(cmd + [a for t in names for a in ("--decl", t)],
                                   cwd=ROOT, capture_output=True, text=True)
        out = (r.stdout + r.stderr).strip()
        print(out)
        if r.returncode:
            held.append((pid, "admit refused", out))
    else:
        held.append((pid, grade, m.group(3).split("|")[0].strip()))
for h in held:
    print("HELD", *h, sep=" | ")
