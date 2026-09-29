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
SCRATCH = Path.home() / ".cache" / "solve-loop"   # survives /tmp cleaning; partial files carry over
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


# Classifications the APM queue also excludes (open_problem_queue.clj): the
# statement is already known to be wrong, or the problem is not a proof task.
SKIP_CLASSES = {"defective", "partial-invalid-statement", "statement-defective",
                "construction-blocked", "out-of-series"}


def classification(pid: str) -> str | None:
    try:
        return json.loads((ROOT / "problems" / pid / "status.json").read_text()).get("classification")
    except (OSError, ValueError):
        return None


def open_problems() -> list[str]:
    out = []
    for p in sorted(os.listdir(ROOT / "problems")):
        f = ROOT / "problems" / p / "lean" / "Main.lean"
        if p.startswith("t") or not f.exists() or classification(p) in SKIP_CLASSES:
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


DECL = re.compile(r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\s+([^\s(:{\[]+)")
TOPLEVEL = re.compile(r"(?m)^(?:@\[|private\s|protected\s|theorem\s|lemma\s|def\s|abbrev\s|"
                      r"instance\s|structure\s|class\s|inductive\s|noncomputable\s|namespace\s|end\b|"
                      r"section\b|open\s|variable\s|#|/--|example\b)")


def statement_decls(text: str) -> list[str]:
    """Every theorem/lemma whose body still contains `sorry`: these are what the
    problem asks to be proved. Non-topology problems have no registry entry and
    no fixed `apm_<id>` name (a96A06's is `taylor_coeffs_tend_to_one`)."""
    code = re.sub(r"/-.*?-/", lambda m: " " * len(m.group(0)), text, flags=re.S)
    code = re.sub(r"--[^\n]*", lambda m: " " * len(m.group(0)), code)
    starts = [m.start() for m in TOPLEVEL.finditer(code)] + [len(code)]
    out = []
    for m in DECL.finditer(code):
        end = next(x for x in starts if x > m.start())
        if code_sorries(code[m.start():end]):
            out.append(m.group(1))
    return out


def pin(pid: str) -> dict:
    text = git("show", f"HEAD:problems/{pid}/lean/Main.lean")
    decls = statement_decls(text)
    # The problem's own theorem is the statement; bridge lemmas are an earlier
    # solver's plan (some are false, like t00J02's Producer), so a seat may
    # drop or restate them as long as the file ends sorry-free.
    main = [d for d in decls if d.lower() == f"apm_{pid.lower()}"]
    decls = main or decls
    if not decls:
        raise ValueError("no theorem or lemma with a sorry found in Main.lean")
    fp = registry.fingerprint(text, decls)
    if "missing" in fp:
        raise ValueError(f"cannot fingerprint {fp['missing']}")
    fp["decls"] = decls
    return fp


def check(pid: str, proposal: Path, pinned: dict) -> tuple[bool, str]:
    """Accept only a sorry-free, standard-axiom proof of the pinned statements."""
    if not proposal.exists():
        return False, f"no proposal at {proposal}"
    text = proposal.read_text()
    fp = registry.fingerprint(text, pinned["decls"])
    if "missing" in fp:
        return False, f"the theorem {fp['missing']} was deleted or renamed; it must stay, exactly as stated"
    if fp.get("sha256") != pinned["sha256"]:
        return False, ("statement changed: the fingerprint of the pinned theorem(s) and the definitions they use "
                       "differs from the pinned statement; restore it exactly")
    if code_sorries(text):
        return False, "proposal still contains sorry"
    probe = proposal.with_name("Check.lean")
    probe.write_text(text + "\n\n" + "".join(f"#print axioms {d}\n" for d in pinned["decls"]))
    r = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT, capture_output=True,
                       text=True, timeout=3600)
    out = r.stdout + r.stderr
    if r.returncode or re.search(r"(?m)^[^\n]*: error", out):
        return False, "does not compile:\n" + "\n".join(out.splitlines()[:40])
    if re.search(r"declaration uses .sorry", out):
        return False, "a declaration still uses sorry"
    found = re.findall(r"depends on axioms: \[([^\]]*)\]", out)
    axioms = {a.strip() for g in found for a in g.split(",")}
    if not axioms <= STANDARD_AXIOMS:
        return False, f"non-standard axioms: {sorted(axioms - STANDARD_AXIOMS)}"
    if len(found) + out.count("does not depend on any axioms") < len(pinned["decls"]):
        return False, "could not read #print axioms output for every pinned declaration"
    return True, f"axioms {sorted(axioms)}"


def conclusion(header: str) -> str:
    """The part of a theorem header after its top-level colon (binders dropped)."""
    depth = 0
    for i, ch in enumerate(header):
        if ch in "([{⦃": depth += 1
        elif ch in ")]}⦄": depth -= 1
        elif ch == ":" and depth == 0 and header[i:i + 2] != ":=":
            return header[i + 1:].strip()
    return header


def squash(t: str) -> str:
    # `Type*` and an explicit `Type u` name the same statement; compare modulo universes.
    t = re.sub(r"\b(Type|Sort)(\*|\s+[a-zA-Z_]\w*|\s+_)", r"\1", t)
    return re.sub(r"\s+", " ", t).strip()


def check_refutation(d: Path, pid: str, pinned: dict) -> tuple[bool, str]:
    """A claimed counterexample counts only if Refute.lean compiles with no
    sorry and standard axioms, and its negation contains the pinned theorem's
    conclusion verbatim (`¬ ∀ binders, <conclusion>`), so `¬ (1 = 2)` cannot
    pass for a refutation."""
    f = d / "Refute.lean"
    if not f.exists():
        return False, "claimed refuted without Refute.lean"
    text = f.read_text()
    if code_sorries(text):
        return False, "Refute.lean contains sorry"
    names = re.findall(r"(?m)^(?:theorem|lemma)\s+([^\s(:{\[]+)[^:]*:\s*¬", text)
    if not names:
        return False, "Refute.lean states no negation (theorem ... : ¬ ...)"
    src = git("show", f"HEAD:problems/{pid}/lean/Main.lean")
    concl = [squash(conclusion(registry.header(src[src.index("theorem " + n):])))
             for n in pinned["decls"] if "theorem " + n in src]
    if not concl or not any(c and c in squash(text) for c in concl):
        return False, "Refute.lean's negation does not contain the pinned theorem's conclusion verbatim"
    probe = d / "RefuteCheck.lean"
    probe.write_text(text + "\n" + "".join(f"#print axioms {n}\n" for n in names))
    r = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT, capture_output=True, text=True, timeout=3600)
    out = r.stdout + r.stderr
    if r.returncode or re.search(r"(?m)^[^\n]*: error", out) or "declaration uses 'sorry'" in out:
        return False, "Refute.lean does not compile cleanly"
    axioms = {a.strip() for g in re.findall(r"depends on axioms: \[([^\]]*)\]", out) for a in g.split(",")}
    if not axioms <= STANDARD_AXIOMS:
        return False, f"Refute.lean uses non-standard axioms {sorted(axioms - STANDARD_AXIOMS)}"
    return True, f"Refute.lean compiles; negations: {names}"


def land(pid: str, proposal: Path, seat: str, job: str) -> str:
    rel = f"problems/{pid}/lean/Main.lean"
    with LOCK:
        shutil.copyfile(proposal, ROOT / rel)
        git("add", "--", rel)
        git("commit", "-q", "-m", f"solve-loop: close {pid} ({seat}, {job})\n\n"
            "Checked by scripts/solve-loop.py: compiles with no sorry, standard axioms only,\n"
            "statement fingerprint unchanged from dispatch.", "--", rel)
        return git("rev-parse", "--short", "HEAD").strip()


PROMPT = """# Prove one problem (solve loop, apm-lean)

Problem: {pid}. Repo: /home/joe/code/apm-lean (shared; read it, do NOT edit, stage or commit there).
Read problems/{pid}/problem.md and problems/{pid}/lean/Main.lean. Prove: {decl}.

Your working file is {out}. {start}
Compile with `cd /home/joe/code/apm-lean && lake env lean {out}` as often as you like.

## Stance (from the APM solver card, v4/v5, which closed the hardest problems)
- This is a substantial proof episode. Use all of it: search Mathlib, try competing routes, build
  missing infrastructure, compile often. Do not stop because one lemma compiled or because the next
  step is long, ugly or bookkeeping-heavy.
- "Not in Mathlib" means construction work, not a reason to stop. Build the smallest truthful
  version in this file (you may also import existing `ConstructionTargets.*` modules). Any new
  definition needs a compiled non-vacuity check: it takes a non-trivial value in a concrete case.
- Before building a prerequisite a plan names, spend a little effort checking whether the target
  closes without it.
- A DEFECT (the statement is false) is the only reason to stop early. Friction is not a defect.

## Hard rules (a script checks these; nothing else is accepted)
- `{decl}` must be present with its statement, and every definition it uses, EXACTLY as in the
  repo file. Deleting, renaming or restating the theorem is refused.
- No `sorry`, `admit`, new `axiom`, `opaque` stand-ins or `native_decide`; standard axioms only.
- Helper and bridge lemmas are yours to rewrite, replace or delete.

## Finishing
- Proved: the file compiles with no sorry. Finish with SOLVE_RESULT proved.
- Statement false: write {dir}/Refute.lean, a file that compiles with no sorry and proves the
  negation of the statement for an explicit counterexample, and explain it in {dir}/REFUTATION.md.
  Finish with SOLVE_RESULT refuted. A refutation without a compiled Refute.lean is not accepted.
- Not finished when the episode ends: leave your best partial file at {out} (the theorem present,
  `sorry` only where work remains; the next seat continues from it) and write the exact residual —
  the remaining Lean obligations and their order — to {dir}/REFUTATION.md. Finish with
  SOLVE_RESULT gave-up.
Do not bell anyone: your final message is read directly from the job record.
{obstruction}{feedback}
Finish with one line: SOLVE_RESULT proved | refuted | gave-up — then one sentence.
"""


STRATEGY_PROMPT = """# Strategy pass for one stalled problem (solve loop, apm-lean)

Problem: {pid}. Repo: /home/joe/code/apm-lean (shared; read it, do NOT edit, stage or commit there).
The solve loop has made {stalls} attempts on {pid} without lowering its `sorry` count (best: {best}).
You are a fresh pair of eyes. Decide whether the next attempts should continue, and on what route.

Read problems/{pid}/problem.md, problems/{pid}/lean/Main.lean, the current partial proof {out}
(compile it: `cd /home/joe/code/apm-lean && lake env lean {out}`), the previous seats' residual
{dir}/REFUTATION.md if present, and the recent refusal reasons and final words below.
Search Mathlib (pinned: .lake/packages/mathlib) and ConstructionTargets/. A newer Mathlib is at
/home/joe/code/mathlib4-latest for SEARCHING only; a result found there must be ported into the
proof file, not imported.

Then say:
1. Exactly where the proof is stuck, in Lean terms (which `sorry`s, what each needs).
2. Whether it is close: would a focused next attempt plausibly remove a `sorry`?
3. The route the next attempts should take: ordered steps, each naming the `sorry` it supplies.
   If the current route is wrong, say so and give a different one. Compile a probe of the
   riskiest step in /tmp/strategy-{pid}/ where you can.
4. If the missing piece is a large body of theory (not a lemma or two), or the statement looks
   false, say so plainly: that is a reason to stop.

Do not edit {out} or anything in the repository. Do not bell anyone: your final message is read
directly from the job record. Finish with one line:
STRATEGY_RESULT continue | stop — then one sentence.

Recent attempts:
{history}
"""


def strategy(seat: str, pid: str, stalls: int, best: int | None) -> tuple[bool, str]:
    """Fresh-eyes pass after a stall (Joe, 2026-09-29: 10 attempts, then strategy).
    Returns (continue?, the seat's plan)."""
    d = SCRATCH / pid
    rows = [r for r in ledger_rows() if r.get("id") == pid][-6:]
    history = "\n".join(f"- attempt {r.get('attempt')}: {r.get('outcome')} {r.get('reason', '')[:200]} | "
                        f"{r.get('said', '')[-300:]}".replace("\r", " ") for r in rows)
    job = dispatch(seat, STRATEGY_PROMPT.format(pid=pid, stalls=stalls, best=best, out=d / "Main.lean",
                                                dir=d, history=history))
    log(f"{seat} <- {pid} strategy ({job})")
    j = wait(job)
    said = j.get("result") or ""
    if not said:
        texts = [e.get("text", "") for e in j.get("events", []) if e.get("type") == "text"]
        said = texts[-1] if texts else ""
    m = re.search(r"STRATEGY_RESULT\s+(continue|stop)", said)
    plan = said[-6000:]
    note = ROOT / "holes" / "labs" / "solve-loop" / "strategy" / f"{pid}.md"
    note.parent.mkdir(parents=True, exist_ok=True)
    note.write_text(f"# {pid} strategy pass ({now()}, {seat}, job {job})\n\n{plan}\n")
    return bool(m and m.group(1) == "continue"), plan


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


def progress_marks(pid: str) -> tuple[int, int] | None:
    """(sorries, sorry-free theorem/lemma bodies) in the partial file, or None if absent.
    An attempt moved the proof if it removed a sorry or proved another declaration
    (splitting a sorry into sub-lemmas and proving some of them counts)."""
    f = SCRATCH / pid / "Main.lean"
    if not f.exists():
        return None
    t = re.sub(r"/-.*?-/", " ", f.read_text(), flags=re.S)
    t = re.sub(r"--[^\n]*", " ", t)
    bodies = re.split(r"(?m)^(?:private |protected )?(?:theorem|lemma) ", t)[1:]
    proved = sum(1 for b in bodies if not re.search(r"(?<![A-Za-z0-9_.])sorry(?![A-Za-z0-9_.])", b))
    return code_sorries(t), proved


def moved(best: int | None, after: tuple[int, int] | None) -> bool:
    """Only a new low in the sorry count counts. Proved helper lemmas do not: on
    2026-09-29 m02J02 went from 30 to 108 proved lemmas over 47 attempts with its
    3 sorries (the three basis bridges) untouched."""
    return after is not None and (best is None or after[0] < best)


def attempt(seat: str, pid: str, feedback: str) -> dict:
    fp = pin(pid)
    d = SCRATCH / pid
    d.mkdir(parents=True, exist_ok=True)
    out = d / "Main.lean"
    for stale in ("REFUTATION.md", "Refute.lean", "Check.lean", "RefuteCheck.lean"):
        (d / stale).unlink(missing_ok=True)
    # Continue from the previous attempt's partial file when it still states
    # the pinned theorem; otherwise start from the repository file.
    if out.exists() and registry.fingerprint(out.read_text(), fp["decls"]).get("sha256") == fp["sha256"]:
        start = ("It already holds the previous seat's partial proof: continue from it "
                 "(the residual below says what remains).")
    else:
        out.write_text(git("show", f"HEAD:problems/{pid}/lean/Main.lean"))
        start = "It starts as a copy of the repository file."
    prior = ROOT / "holes" / "labs" / "solve-loop" / "obstructions" / f"{pid}.md"
    obstruction = (f"\nResidual left by the previous seat (continue from it; do not stop for the same reason):\n"
                   f"{prior.read_text()[:4000]}\n") if prior.exists() else ""
    plan = ROOT / "holes" / "labs" / "solve-loop" / "strategy" / f"{pid}.md"
    if plan.exists():
        obstruction += (f"\nA strategy pass reviewed this problem after it stalled. Follow its route "
                        f"unless you find it wrong:\n{plan.read_text()[-4000:]}\n")
    prompt = PROMPT.format(pid=pid, decl=", ".join(fp["decls"]), out=out, dir=d, obstruction=obstruction, start=start,
                           feedback=(f"\nA previous attempt was refused by the checker:\n{feedback}\n" if feedback else ""))
    job = dispatch(seat, prompt)
    log(f"{seat} <- {pid} ({job})")
    j = wait(job)
    row = {"id": pid, "seat": seat, "job": job, "pinned": fp["sha256"], "state": j.get("state"),
           "at": now(), "said": (j.get("result") or "")[-300:]}
    claimed = re.search(r"SOLVE_RESULT\s+(\w[\w-]*)", row["said"])
    refuted = claimed and claimed.group(1) == "refuted"
    if refuted:
        ok_r, why_r = check_refutation(d, pid, fp)
        row["refutation-check"] = why_r
        refuted = ok_r
    if refuted:
        shutil.copytree(d, ROOT / "holes" / "labs" / "solve-loop" / "refutations" / pid, dirs_exist_ok=True)
        row.update(outcome="refuted-claim", reason="compiled refutation (Refute.lean: no sorry, standard axioms; that it negates the pinned statement is unchecked) copied under holes/labs/solve-loop/refutations/")
        return row
    # A give-up is not a refutation (2026-09-28: 12 of 16 REFUTATION.md files
    # were obstruction notes, "no counterexample was found"). Keep the note and
    # hand it to the next attempt instead of retiring the problem.
    if (d / "REFUTATION.md").exists():
        note = ROOT / "holes" / "labs" / "solve-loop" / "obstructions" / f"{pid}.md"
        note.parent.mkdir(parents=True, exist_ok=True)
        note.write_text((d / "REFUTATION.md").read_text())
    ok, why = check(pid, out, fp)
    if ok:
        row.update(outcome="landed", commit=land(pid, out, seat, job), reason=why)
    else:
        row.update(outcome="refused", reason=why)
    return row


def worker(seat: str, todo: list[str], attempts: int, budget: list[int], stall_limit: int,
           strategy_seat: str, max_strategy: int) -> None:
    while True:
        with LOCK:
            if not todo or budget[0] <= 0:
                return
            pid = todo.pop(0)
        feedback = ""
        stalls = 0
        passes = 0
        start = progress_marks(pid)
        best = start[0] if start else None
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
            after = progress_marks(pid)
            row["marks"] = after
            record(row)
            log(f"{seat} {pid} attempt {n+1}: {row['outcome']} {row.get('commit', '')} {row.get('reason', '')[:160]}")
            if row["outcome"] in ("landed", "refuted-claim"):
                break
            if "usage limit" in row.get("said", "") or "quota" in row.get("said", ""):
                log(f"{seat}: provider quota reached; stopping this seat")
                return
            feedback = row.get("reason", "")
            # Joe, 2026-09-29: continue while the proof moves, stop when it repeats.
            if moved(best, after):
                best, stalls = after[0], 0
            else:
                stalls += 1
            if stalls >= stall_limit:
                go = False
                if passes < max_strategy:
                    passes += 1
                    try:
                        go, plan = strategy(strategy_seat, pid, stalls, best)
                    except Exception as e:
                        plan = f"strategy pass failed: {e}"
                    record({"id": pid, "seat": strategy_seat, "at": now(), "outcome": "strategy",
                            "decision": "continue" if go else "stop", "said": plan[-300:]})
                    log(f"{strategy_seat} {pid} strategy pass {passes}: {'continue' if go else 'stop'}")
                if not go:
                    log(f"{seat} {pid}: {stalls} attempts without a new low in its sorry count "
                        f"(best {best}, marks {after}); leaving it")
                    break
                stalls = 0


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("queue")
    r = sub.add_parser("run")
    r.add_argument("--seats", required=True)
    r.add_argument("--max-jobs", type=int, default=600)
    r.add_argument("--attempts", type=int, default=50, help="cap per problem")
    r.add_argument("--stall", type=int, default=10,
                   help="stop a problem after this many attempts without a new low in its sorry count")
    r.add_argument("--strategy-seat", default="solve-strategy",
                   help="fresh seat asked, after each stall, whether and how to continue")
    r.add_argument("--max-strategy", type=int, default=2, help="strategy passes per problem")
    r.add_argument("--only", help="comma-separated problem ids")
    r.add_argument("--skip", help="comma-separated problem ids to leave alone")
    o = ap.parse_args()
    finished = {x["id"] for x in ledger_rows() if x.get("outcome") in ("landed", "refuted-claim")}
    todo = [p for p in open_problems() if p not in finished]
    if o.cmd == "queue":
        print(f"{len(todo)} open non-topology problems not yet landed or refuted:")
        print(" ".join(todo))
        return 0
    if o.only:
        todo = [p for p in o.only.split(",") if p in todo]
    if o.skip:
        todo = [p for p in todo if p not in o.skip.split(",")]
    budget = [o.max_jobs]
    threads = [threading.Thread(target=worker, args=(s.strip(), todo, o.attempts, budget, o.stall,
                                                          o.strategy_seat, o.max_strategy))
               for s in o.seats.split(",") if s.strip()]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    log("solve loop finished")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
