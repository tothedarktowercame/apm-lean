#!/usr/bin/env python3
"""Bulk-import futon6 proof-frame workspaces into apm-lean problem bundles.

Default behavior is conservative:
- additive
- skips targets that already exist
- preserves duplicate-frame candidate layout chosen by the single-frame importer
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FUTON6_ROOT = REPO_ROOT.parent / "futon6"
IMPORTER = REPO_ROOT / "scripts" / "import-proof-frame.py"


def discover_workspaces(futon6_root: Path) -> list[Path]:
    proof_frames_root = futon6_root / ".state" / "proof-frames"
    if not proof_frames_root.exists():
        return []
    return sorted(proof_frames_root.glob("*/*/workspace.json"))


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--futon6-root", type=Path, default=DEFAULT_FUTON6_ROOT)
    ap.add_argument("--problem-id", action="append", default=[],
                    help="Restrict to one or more problem ids")
    ap.add_argument("--limit", type=int, default=0,
                    help="Import at most N workspace bundles")
    ap.add_argument("--force", action="store_true",
                    help="Pass --force through to the per-frame importer")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    workspaces = discover_workspaces(args.futon6_root.resolve())

    if args.problem_id:
        allowed = set(args.problem_id)
        workspaces = [p for p in workspaces if p.parent.parent.name in allowed]

    if args.limit and args.limit > 0:
        workspaces = workspaces[:args.limit]

    imported = 0
    skipped = 0
    failed = 0

    for workspace in workspaces:
        cmd = [sys.executable, str(IMPORTER), str(workspace)]
        if args.force:
            cmd.append("--force")

        proc = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )

        if proc.returncode == 0:
            imported += 1
            print(f"[imported] {workspace}")
            continue

        stderr = (proc.stderr or "").strip()
        stdout = (proc.stdout or "").strip()
        msg = stderr or stdout

        if "bundle exists:" in msg:
            skipped += 1
            print(f"[skipped]  {workspace}")
            continue

        failed += 1
        print(f"[failed]   {workspace}", file=sys.stderr)
        if stdout:
            print(stdout, file=sys.stderr)
        if stderr:
            print(stderr, file=sys.stderr)

    total = len(workspaces)
    print()
    print(f"total={total} imported={imported} skipped={skipped} failed={failed}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
