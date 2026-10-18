#!/usr/bin/env python3
"""Bring problems/t*/status.json into line with the committed Lean files.

The topology loop closes problems by committing Lean, but nothing updated the
bundle status afterwards: on 2026-09-28, 10 closed problems still recorded
remaining sorries (t96J07 among them) and 39 bundles with a lean/Main.lean said
"informal-only" with `lean.main: null`. Anything crediting closures from
status.json -- open_problem_queue.clj's derive-queue reads it -- saw the wrong
corpus.

Counts are read at a git revision (default HEAD), never from the working tree:
the canonical checkout is shared with running Codex seats, and a half-written
Main.lean must not be credited. `sorry`/`admit` are counted as code, with
comments stripped, the same rule as the topology watcher.

Only the `lean` block and `classification` are touched; every other key is
kept. A status.json with uncommitted edits in the working tree is skipped.

  refresh-topology-status.py            rewrite changed files, print their paths
  refresh-topology-status.py --check    print what would change, exit 1 if any
  refresh-topology-status.py --prefix ""  every problem, not only t*

A placeholder-free problem is "complete" only if its statement matches an
approved entry in problems/STATEMENTS.json (scripts/statement-registry.py);
otherwise "closed-unregistered" or "closed-statement-mismatch".
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOK = re.compile(r"\b(sorry|admit)\b")
# Kept when the bundle has no remaining placeholder: all mean "closed".
CLOSED_CLASSES = {"complete", "solved", "proved", "compiled"}
# Set by this script when a placeholder-free statement is not an approved,
# matching registry entry; never kept across a refresh.
# Kept while placeholders remain: they carry information a count cannot.
OPEN_CLASSES = {"partial", "partial-banked", "partial-lean-proof", "construction-blocked",
                "defective", "partial-invalid-statement", "statement-defective"}


def git(*args: str) -> str:
    r = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True)
    if r.returncode:
        raise SystemExit(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def placeholders(src: str) -> int:
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    return len(TOK.findall("\n".join(l.split("--", 1)[0] for l in src.splitlines())))


def _registry():
    import importlib.util
    spec = importlib.util.spec_from_file_location("statement_registry", ROOT / "scripts" / "statement-registry.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def statement_state(pid: str, lean: dict[str, str]) -> str:
    """registered | mismatch | unregistered, against problems/STATEMENTS.json."""
    reg = _registry()
    entry = reg.load()["entries"].get(pid)
    if not entry:
        return "unregistered"
    fp = reg.fingerprint(lean.get("lean/Main.lean", ""), entry["decls"])
    return "registered" if fp.get("sha256") == entry["sha256"] else "mismatch"


def refreshed(status: dict, lean: dict[str, str], pid: str = "") -> dict:
    new = dict(status)
    main = lean.get("lean/Main.lean")
    total = sum(placeholders(s) for s in lean.values())
    main_n = placeholders(main) if main is not None else 0
    new["lean"] = {**(status.get("lean") or {}),
                   "main": "lean/Main.lean" if main is not None else None,
                   "files": sorted(lean),
                   "sorry_count_main": main_n,
                   "sorry_count_scratch": total - main_n,
                   "sorry_count_total": total}
    cls = status.get("classification")
    if not lean:
        new["classification"] = cls or "informal-only"
    elif total == 0:
        # No placeholders is not closure: the statement must be an approved
        # registry entry (Joe, 2026-09-28). Otherwise the proof stands but the
        # problem is not credited.
        state = statement_state(pid, lean)
        if state == "registered":
            new["classification"] = cls if cls in CLOSED_CLASSES else "complete"
        elif state == "mismatch":
            new["classification"] = "closed-statement-mismatch"
        else:
            new["classification"] = "closed-unregistered"
    else:
        new["classification"] = cls if cls in OPEN_CLASSES else "partial"
    return new


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default="HEAD")
    ap.add_argument("--check", action="store_true")
    # The m*/b* bundles had the same gap: 56 closed in September still said
    # open on 2026-10-18.  "" covers every problem.
    ap.add_argument("--prefix", default="t", help='problem-id prefix to refresh ("" = all)')
    a = ap.parse_args()
    names = git("ls-tree", "-r", "--name-only", a.rev, "problems/").splitlines()
    by_problem: dict[str, list[str]] = {}
    for n in names:
        parts = n.split("/")
        if len(parts) >= 3 and parts[1].startswith(a.prefix):
            by_problem.setdefault(parts[1], []).append(n)
    dirty = set(git("status", "--porcelain", "--", "problems/").splitlines())
    changed = []
    for pid, paths in sorted(by_problem.items()):
        spath = f"problems/{pid}/status.json"
        if spath not in paths:
            continue
        if any(line.endswith(spath) for line in dirty):
            print(f"skip {spath}: uncommitted edits", file=sys.stderr)
            continue
        status = json.loads(git("show", f"{a.rev}:{spath}"))
        prefix = f"problems/{pid}/"
        lean = {p[len(prefix):]: git("show", f"{a.rev}:{p}")
                for p in paths if p.startswith(prefix + "lean/") and p.endswith(".lean")}
        new = refreshed(status, lean, pid)
        if new != status:
            changed.append(spath)
            if a.check:
                old_l, new_l = status.get("lean") or {}, new["lean"]
                print(f"{spath}: {status.get('classification')} -> {new['classification']}, "
                      f"sorries {old_l.get('sorry_count_total')} -> {new_l['sorry_count_total']}")
            else:
                (ROOT / spath).write_text(json.dumps(new, indent=2, ensure_ascii=False) + "\n")
                print(spath)
    return 1 if (a.check and changed) else 0


if __name__ == "__main__":
    raise SystemExit(main())
