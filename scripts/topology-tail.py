#!/usr/bin/env python3
"""Follow both topology loops in one readable stream (read-only).

  scripts/topology-tail.py            follow from now (last 15 events first)
  scripts/topology-tail.py --since 2h  replay the last two hours, then follow

Prints one line per event: a row dispatched to a seat, a job finished (with the
start of the seat's finding), a receipt applied, a stop; and a line whenever a
commit changes a problem's `sorry` count. Heartbeats and JSON noise are dropped.
It reads the loops' own logs and git; it never touches a seat or the ledger.
"""
from __future__ import annotations

import argparse
import datetime as dt
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TC = ROOT / "holes" / "labs" / "topology-contract"
LOGS = {"topo1": TC / "runs" / "build-loop.log", "topo2": TC / "runs2" / "build-loop.log"}
SUP = {"topo1": TC / "runs" / "supervisor.log", "topo2": TC / "runs2" / "supervisor.log"}
LINE = re.compile(r"^\[(\S+)\] (.*)$")


def finding(path: str) -> str:
    try:
        t = Path(path).read_text(errors="replace")
    except OSError:
        return ""
    m = re.search(r":outcome (:\S+)", t)
    f = re.search(r':(?:finding|residual|summary) "((?:[^"\\]|\\.){0,600})', t)
    r = re.search(r":reason (:\S+)", t)
    out = (m.group(1) if m else "") + (" " + r.group(1) if r else "")
    if f:
        out += " — " + f.group(1).replace("\\n", " ")[:240]
    return out.strip()


def render(loop: str, text: str) -> str | None:
    if "heartbeat" in text or text.startswith("{") or "items OK" in text:
        return None
    m = re.match(r"(\w+)\((\S+)\) dispatch to (\S+)", text)
    if m:
        return f"{loop} → {m.group(3)} {m.group(1)}: {m.group(2)}"
    m = re.match(r"(\w+)\((\S+)\) done job=\S+ result=(\S+)", text)
    if m:
        return f"{loop} ✓ {m.group(1)} {m.group(2)}  {finding(m.group(3))}"
    if re.match(r"\w+\(\S+\) job=", text):
        return None
    if text.startswith(("applied", "STOP", "WARNING", "seats resolved", "canonical worktree", "supervisor")):
        return f"{loop}   {text[:220]}"
    return None


def sorry_count(rev: str, path: str) -> int | None:
    r = subprocess.run(["git", "-C", str(ROOT), "show", f"{rev}:{path}"], capture_output=True, text=True)
    if r.returncode:
        return None
    t = re.sub(r"/-.*?-/", " ", r.stdout, flags=re.S)
    t = re.sub(r"--[^\n]*", " ", t)
    return len(re.findall(r"(?<![A-Za-z0-9_.])sorry(?![A-Za-z0-9_.])", t))


def new_commits(since: str) -> list[tuple[str, str, str]]:
    r = subprocess.run(["git", "-C", str(ROOT), "log", "--reverse", f"{since}..HEAD", "--format=%h %ad %s",
                        "--date=format-local:%H:%M"], capture_output=True, text=True)
    return [tuple(l.split(" ", 2)) for l in r.stdout.splitlines() if l]


def commit_lines(sha: str, subject: str, when: str) -> list[str]:
    files = subprocess.run(["git", "-C", str(ROOT), "diff-tree", "--no-commit-id", "--name-only", "-r", sha],
                           capture_output=True, text=True).stdout.split()
    out = []
    for f in files:
        m = re.match(r"problems/(t[^/]+)/lean/Main\.lean$", f)
        if m:
            before, after = sorry_count(f"{sha}^", f), sorry_count(sha, f)
            if before != after:
                tag = "CLOSED" if after == 0 else f"sorry {before}→{after}"
                out.append(f"{when} ★ {m.group(1)} {tag}  ({sha} {subject[:90]})")
    if not out and not subject.startswith("topology-loop:") and any(
            f.startswith(("problems/t", "ConstructionTargets")) for f in files):
        out.append(f"{when} + {sha} {subject[:120]}")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--since", help="replay window, e.g. 30m, 2h")
    o = ap.parse_args()
    cutoff = None
    if o.since:
        n, u = int(o.since[:-1]), o.since[-1]
        cutoff = dt.datetime.now(dt.timezone.utc) - dt.timedelta(**{{"m": "minutes", "h": "hours"}[u]: n})
    # replay
    events = []
    for loop, p in list(LOGS.items()) + list(SUP.items()):
        if not p.exists():
            continue
        for l in p.read_text(errors="replace").splitlines():
            m = LINE.match(l)
            if not m:
                continue
            ts = dt.datetime.fromisoformat(m.group(1).replace("Z", "+00:00"))
            if cutoff and ts < cutoff:
                continue
            s = render(loop, m.group(2))
            if s:
                events.append((ts, f"{ts:%H:%M} {s}"))
    events.sort()
    for _, s in (events if cutoff else events[-15:]):
        print(s, flush=True)
    head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if cutoff:
        base = subprocess.run(["git", "-C", str(ROOT), "rev-list", "-1", f"--before={cutoff.isoformat()}", "HEAD"],
                              capture_output=True, text=True).stdout.strip()
        for sha, when, subj in new_commits(base):
            for s in commit_lines(sha, subj, when):
                print(s, flush=True)
    # follow
    pos = {p: p.stat().st_size for p in list(LOGS.values()) + list(SUP.values()) if p.exists()}
    names = {**{v: k for k, v in LOGS.items()}, **{v: k for k, v in SUP.items()}}
    while True:
        for p, loop in names.items():
            if not p.exists():
                continue
            size = p.stat().st_size
            start = pos.get(p, 0)
            if size < start:
                start = 0
            if size > start:
                with p.open(errors="replace") as fh:
                    fh.seek(start)
                    for l in fh.read().splitlines():
                        m = LINE.match(l)
                        s = m and render(loop, m.group(2))
                        if s:
                            print(f"{m.group(1)[11:16]} {s}", flush=True)
                pos[p] = size
        now = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
        if now and now != head:
            for sha, when, subj in new_commits(head):
                for s in commit_lines(sha, subj, when):
                    print(s, flush=True)
            head = now
        time.sleep(10)


if __name__ == "__main__":
    raise SystemExit(main())
