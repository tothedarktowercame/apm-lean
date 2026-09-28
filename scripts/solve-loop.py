#!/usr/bin/env python3
"""Plain solve loop for the non-topology problems (Joe, 2026-09-28).

No frames, cascade, mining or transfer: one Codex job per problem, checked by
this script, committed by this script.

  solve-loop.py queue                       list open problems, change nothing
  solve-loop.py run --seats codex-5,codex-6 [--max-jobs N] [--attempts 2]

Per problem:
1. Pin the statement: sha256 fingerprint of `theorem apm_<id>` plus the
   same-file definitions it reaches (statement-registry.py's fingerprint), at
   HEAD, when the job is sent.
2. The seat writes a complete proposed Main.lean to
   /tmp/solve-loop/<id>/Main.lean. It never edits or commits the repository, so
   the shared tree is never held dirty while a job runs.
3. This script accepts the proposal only if it compiles with no errors and no
   `sorry` warning, `#print axioms` shows only propext / Classical.choice /
   Quot.sound, and the statement fingerprint equals the pin. A statement
   changed in any way -- the topology loop's failure -- is refused.
4. Accepted proposals are copied over problems/<id>/lean/Main.lean and
   committed path-scoped at once. A refusal is fed back to the next attempt.

State: holes/labs/solve-loop/ledger.jsonl (one line per attempt).
"""
from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "holes" / "labs" / "solve-loop" / "ledger.jsonl"
SCRATCH = Path("/tmp/solve-loop")
AGENCY = "http://localhost:7070"
SEND = "/home/joe/code/futon3c/scripts/agency_send.py"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TERMINAL = {"done", "failed", "error", "cancelled", "timeout", "timed-out"}
JOB_TIMEOUT = int(os.environ.get("SOLVE_JOB_TIMEOUT", 3 * 3600))
LOCK = threading.Lock()   # git + ledger writes

_spec = importlib.util.spec_from_file_location("registry", ROOT / "scripts" / "statement-registry.py")
registry = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(registry)


def now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def log(msg: str) -> None:
    print(f"[{now()}] {msg}", flush=True)


def git(*args: str, check: bool = True) -> str:
    r = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True)
    if check and r.returncode:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def code_sorries(text: str) -> int:
    t = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    t = re.sub(r"--[^\n]*", " ", t)
    return len(re.findall(r"(?<![A-Za-z0-9_.])sorry(?![A-Za-z0-9_.])", t))


def open_problems() -> list[str]:
    out = []
    for p in sorted(os.listdir(ROOT / "problems")):
        f = ROOT / "problems" / p / "lean" / "Main.lean"
        if p.startswith("t") or not f.exists():
            continue
        if code_sorries(git("show", f"HEAD:problems/{p}/lean/Main.lean", check=False)) > 0:
            out.append(p)
    return out


def ledger_rows() -> list[dict]:
    if not LEDGER.exists():
        return []
    return [json.loads(l) for l in LEDGER.read_text().splitlines() if l.strip()]


def record(row: dict) -> None:
    with LOCK:
        LEDGER.parent.mkdir(parents=True, exist_ok=True)
        with LEDGER.open("a") as fh:
            fh.write(json.dumps(row, ensure_ascii=False) + "\n")


def pin(pid: str) -> dict:
    fp = registry.fingerprint(registry.main_src(pid, "HEAD"), registry.default_decls(pid))
    if "missing" in fp:
        raise ValueError(f"no theorem {fp['missing']} in Main.lean")
    return fp


def check(pid: str, proposal: Path, pinned: str) -> tuple[bool, str]:
    """Accept only a sorry-free, standard-axiom proof of the pinned statement."""
    if not proposal.exists():
        return False, f"no proposal at {proposal}"
    text = proposal.read_text()
    fp = registry.fingerprint(text, registry.default_decls(pid))
    if fp.get("sha256") != pinned:
        return False, ("statement changed: the fingerprint of apm_<id> and the definitions it uses "
                       "differs from the pinned statement; restore it exactly")
    if code_sorries(text):
        return False, "proposal still contains sorry"
    probe = proposal.with_name("Check.lean")
    probe.write_text(text + f"\n\n#print axioms {registry.default_decls(pid)[0]}\n")
    r = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT, capture_output=True,
                       text=True, timeout=3600)
    out = r.stdout + r.stderr
    if r.returncode or re.search(r"(?m)^[^\n]*: error", out):
        return False, "does not compile:\n" + "\n".join(out.splitlines()[:40])
    if re.search(r"declaration uses .sorry", out):
        return False, "a declaration still uses sorry"
    m = re.search(r"depends on axioms: \[([^\]]*)\]", out)
    axioms = {a.strip() for a in m.group(1).split(",")} if m else set()
    if m and not axioms <= STANDARD_AXIOMS:
        return False, f"non-standard axioms: {sorted(axioms - STANDARD_AXIOMS)}"
    if not m and "does not depend on any axioms" not in out:
        return False, "could not read #print axioms output"
    return True, f"axioms {sorted(axioms)}"


def land(pid: str, proposal: Path, seat: str, job: str) -> str:
    rel = f"problems/{pid}/lean/Main.lean"
    with LOCK:
        shutil.copyfile(proposal, ROOT / rel)
        git("add", "--", rel)
        git("commit", "-q", "-m", f"solve-loop: close apm_{pid.lower()} ({seat}, {job})\n\n"
            "Checked by scripts/solve-loop.py: compiles with no sorry, standard axioms only,\n"
            "statement fingerprint unchanged from dispatch.", "--", rel)
        return git("rev-parse", "--short", "HEAD").strip()


PROMPT = """# Prove one problem (solve loop, apm-lean)

Problem: {pid}. Repo: /home/joe/code/apm-lean (shared; read it, do NOT edit, stage or commit there).

Read problems/{pid}/problem.md and problems/{pid}/lean/Main.lean. Prove `theorem {decl}`.

Write your COMPLETE proposed Main.lean to {out} (create the directory) and compile it with
`cd /home/joe/code/apm-lean && lake env lean {out}` until it succeeds. Rules:
- The statement of `{decl}` and every definition it uses must stay EXACTLY as in the repo file
  (a fingerprint check refuses any change, including to hypotheses, types or definitions).
- No `sorry`, `admit`, `axiom`, `opaque` stand-ins, or `native_decide`; standard axioms only.
- You may add helper lemmas and imports to the file, above the theorem.
- Everything goes in this one file; do not create modules elsewhere.
- If the statement is false or unprovable as written, do not change it: write your evidence
  (ideally a compiled counterexample) to {dir}/REFUTATION.md and stop.
{feedback}
Finish with one line: SOLVE_RESULT proved | refuted | gave-up — then one sentence.
"""


def dispatch(seat: str, prompt: str) -> str:
    r = subprocess.run([sys.executable, SEND, "--from", "solve-loop", "--to", seat, "--kind", "bell",
                        "--mode", "work"], input=prompt, capture_output=True, text=True)
    m = re.search(r'"job-id":"([^"]+)"', r.stdout)
    if not m:
        raise RuntimeError(f"dispatch to {seat} failed: {r.stdout[-400:]} {r.stderr[-400:]}")
    return m.group(1)


def wait(job: str) -> dict:
    start = time.time()
    while time.time() - start < JOB_TIMEOUT:
        try:
            with urllib.request.urlopen(f"{AGENCY}/api/alpha/invoke/jobs/{job}", timeout=30) as fh:
                j = json.load(fh).get("job", {})
            if j.get("state") in TERMINAL:
                return j
        except Exception as e:  # transient Agency hiccup: keep waiting
            log(f"status {job}: {e}")
        time.sleep(60)
    return {"state": "timeout"}


def attempt(seat: str, pid: str, feedback: str) -> dict:
    fp = pin(pid)
    d = SCRATCH / pid
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir(parents=True)
    out = d / "Main.lean"
    prompt = PROMPT.format(pid=pid, decl=registry.default_decls(pid)[0], out=out, dir=d,
                           feedback=(f"\nA previous attempt was refused by the checker:\n{feedback}\n" if feedback else ""))
    job = dispatch(seat, prompt)
    log(f"{seat} <- {pid} ({job})")
    j = wait(job)
    row = {"id": pid, "seat": seat, "job": job, "pinned": fp["sha256"], "state": j.get("state"),
           "at": now(), "said": (j.get("result") or "")[-300:]}
    if (d / "REFUTATION.md").exists():
        shutil.copytree(d, ROOT / "holes" / "labs" / "solve-loop" / "refutations" / pid, dirs_exist_ok=True)
        row.update(outcome="refuted-claim", reason="seat wrote REFUTATION.md (copied under holes/labs/solve-loop/refutations/)")
        return row
    ok, why = check(pid, out, fp["sha256"])
    if ok:
        row.update(outcome="landed", commit=land(pid, out, seat, job), reason=why)
    else:
        row.update(outcome="refused", reason=why)
    return row


def worker(seat: str, todo: list[str], attempts: int, budget: list[int]) -> None:
    while True:
        with LOCK:
            if not todo or budget[0] <= 0:
                return
            pid = todo.pop(0)
        feedback = ""
        for n in range(attempts):
            with LOCK:
                if budget[0] <= 0:
                    return
                budget[0] -= 1
            try:
                row = attempt(seat, pid, feedback)
            except Exception as e:
                row = {"id": pid, "seat": seat, "at": now(), "outcome": "error", "reason": str(e)[:500]}
            row["attempt"] = n + 1
            record(row)
            log(f"{seat} {pid} attempt {n+1}: {row['outcome']} {row.get('commit', '')} {row.get('reason', '')[:160]}")
            if row["outcome"] in ("landed", "refuted-claim"):
                break
            if "usage limit" in row.get("said", "") or "quota" in row.get("said", ""):
                log(f"{seat}: provider quota reached; stopping this seat")
                return
            feedback = row.get("reason", "")


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("queue")
    r = sub.add_parser("run")
    r.add_argument("--seats", required=True)
    r.add_argument("--max-jobs", type=int, default=200)
    r.add_argument("--attempts", type=int, default=2)
    r.add_argument("--only", help="comma-separated problem ids")
    o = ap.parse_args()
    finished = {x["id"] for x in ledger_rows() if x.get("outcome") in ("landed", "refuted-claim")}
    todo = [p for p in open_problems() if p not in finished]
    if o.cmd == "queue":
        print(f"{len(todo)} open non-topology problems not yet landed or refuted:")
        print(" ".join(todo))
        return 0
    if o.only:
        todo = [p for p in o.only.split(",") if p in todo]
    budget = [o.max_jobs]
    threads = [threading.Thread(target=worker, args=(s.strip(), todo, o.attempts, budget))
               for s in o.seats.split(",") if s.strip()]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    log("solve loop finished")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
