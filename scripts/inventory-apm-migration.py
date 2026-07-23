#!/usr/bin/env python3
"""Inventory the current APM migration surface across apm-lean and futon6.

Outputs:
- JSON inventory for tooling
- Markdown summary for human review
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FUTON6_ROOT = REPO_ROOT.parent / "futon6"
DEFAULT_JSON_OUT = REPO_ROOT / "docs" / "generated" / "apm-migration-inventory.json"
DEFAULT_MD_OUT = REPO_ROOT / "docs" / "generated" / "apm-migration-inventory.md"

IGNORED_LEAN_PROOF_DIRS = {"worked", "runner-pilot-attempt1", "runner-pilot-attempt2"}


def now_utc() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def rel(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT.resolve()))
    except ValueError:
        return str(path.resolve())


def discover_frame_records(futon6_root: Path) -> list[dict]:
    records: list[dict] = []
    proof_frames_root = futon6_root / ".state" / "proof-frames"
    if not proof_frames_root.exists():
        return records

    for workspace_json in sorted(proof_frames_root.glob("*/*/workspace.json")):
        metadata = read_json(workspace_json)
        problem_id = metadata.get("proof/problem-id")
        frame_id = metadata.get("frame/id")
        generated_at = metadata.get("workspace/generated-at")
        frame_root = workspace_json.parent
        receipt_path = frame_root.parent / f"{frame_id}.json"
        records.append({
            "problem_id": problem_id,
            "frame_id": frame_id,
            "generated_at": generated_at,
            "workspace_json": str(workspace_json.resolve()),
            "frame_root": str(frame_root.resolve()),
            "lean_root": metadata.get("frame/lean-root"),
            "module_root": metadata.get("frame/module-root"),
            "has_receipt": receipt_path.exists(),
            "receipt_path": str(receipt_path.resolve()) if receipt_path.exists() else None,
            "artifacts": metadata.get("artifacts", {}),
        })
    return records


def discover_legacy_lean_proofs() -> set[str]:
    root = REPO_ROOT / "lean-proofs"
    if not root.exists():
        return set()
    return {
        p.name
        for p in root.iterdir()
        if p.is_dir() and p.name not in IGNORED_LEAN_PROOF_DIRS
    }


def discover_problem_bundles() -> set[str]:
    root = REPO_ROOT / "problems"
    if not root.exists():
        return set()
    return {p.name for p in root.iterdir() if p.is_dir()}


def has_reconciled_legacy_source(problem_id: str) -> bool:
    problem_root = REPO_ROOT / "problems" / problem_id
    if not problem_root.exists():
        return False

    archive_root = problem_root / "historical" / "legacy-lean-proofs"
    if archive_root.exists():
        return True

    status_path = problem_root / "status.json"
    if not status_path.exists():
        return False

    try:
        status = read_json(status_path)
    except json.JSONDecodeError:
        return False

    if status.get("source", {}).get("kind") == "legacy-lean-proofs":
        return True

    for entry in status.get("historical_sources", []):
        if entry.get("kind") == "legacy-lean-proofs":
            return True

    return False


def choose_latest_frame(frames: list[dict]) -> dict | None:
    if not frames:
        return None
    return sorted(
        frames,
        key=lambda rec: (
            rec.get("generated_at") or "",
            rec.get("frame_id") or "",
        ),
        reverse=True,
    )[0]


def build_inventory(futon6_root: Path) -> dict:
    frame_records = discover_frame_records(futon6_root)
    legacy_lean_proofs = discover_legacy_lean_proofs()
    problem_bundles = discover_problem_bundles()

    by_problem: dict[str, list[dict]] = defaultdict(list)
    for rec in frame_records:
        by_problem[rec["problem_id"]].append(rec)

    problem_ids = sorted(set(by_problem) | legacy_lean_proofs | problem_bundles)
    problems: list[dict] = []

    for problem_id in problem_ids:
        frames = sorted(by_problem.get(problem_id, []), key=lambda rec: rec["frame_id"] or "")
        latest = choose_latest_frame(frames)
        frame_ids = [rec["frame_id"] for rec in frames]
        receipt_count = sum(1 for rec in frames if rec["has_receipt"])
        imported_bundle_exists = problem_id in problem_bundles
        legacy_lean_exists = problem_id in legacy_lean_proofs
        legacy_reconciled = has_reconciled_legacy_source(problem_id)

        problems.append({
            "problem_id": problem_id,
            "frame_count": len(frames),
            "frame_ids": frame_ids,
            "receipt_count": receipt_count,
            "latest_frame_id": latest["frame_id"] if latest else None,
            "latest_generated_at": latest.get("generated_at") if latest else None,
            "latest_workspace_json": latest.get("workspace_json") if latest else None,
            "latest_receipt_path": latest.get("receipt_path") if latest else None,
            "imported_bundle_exists": imported_bundle_exists,
            "legacy_lean_proof_exists": legacy_lean_exists,
            "legacy_reconciled": legacy_reconciled,
        })

    duplicate_problems = [p for p in problems if p["frame_count"] > 1]
    frame_backed_problems = [p for p in problems if p["frame_count"] > 0]
    migrated_problems = [p for p in problems if p["imported_bundle_exists"]]

    return {
        "generated_at": now_utc(),
        "schema": "apm-migration-inventory.v1",
        "counts": {
            "frame_records": len(frame_records),
            "frame_backed_problems": len(frame_backed_problems),
            "duplicate_frame_problems": len(duplicate_problems),
            "imported_problem_bundles": len(migrated_problems),
            "legacy_lean_proof_dirs": len(legacy_lean_proofs),
            "legacy_reconciled_problems": sum(1 for p in problems if p["legacy_reconciled"]),
        },
        "duplicate_problems": sorted(
            duplicate_problems,
            key=lambda p: (p["frame_count"], p["problem_id"]),
            reverse=True,
        ),
        "problems": problems,
    }


def render_markdown(inv: dict) -> str:
    counts = inv["counts"]
    lines = [
        "# APM Migration Inventory",
        "",
        f"Generated: `{inv['generated_at']}`",
        "",
        "## Summary",
        "",
        f"- frame records: `{counts['frame_records']}`",
        f"- frame-backed problems: `{counts['frame_backed_problems']}`",
        f"- duplicate-frame problems: `{counts['duplicate_frame_problems']}`",
        f"- imported problem bundles: `{counts['imported_problem_bundles']}`",
        f"- legacy lean-proof dirs: `{counts['legacy_lean_proof_dirs']}`",
        f"- legacy sources reconciled into problems/: `{counts['legacy_reconciled_problems']}`",
        "",
        "## Duplicate-Frame Problems",
        "",
    ]

    if not inv["duplicate_problems"]:
        lines.append("None.")
    else:
        for problem in inv["duplicate_problems"]:
            lines.append(
                f"- `{problem['problem_id']}`: {problem['frame_count']} frames; "
                f"latest `{problem['latest_frame_id']}`; "
                f"bundle={'yes' if problem['imported_bundle_exists'] else 'no'}; "
                f"legacy-lean={'yes' if problem['legacy_lean_proof_exists'] else 'no'}; "
                f"legacy-reconciled={'yes' if problem['legacy_reconciled'] else 'no'}"
            )

    lines.extend([
        "",
        "## Problem Table",
        "",
        "| Problem | Frames | Latest Frame | Bundle | Legacy Lean | Legacy Reconciled |",
        "|---|---:|---|---|---|---|",
    ])

    for problem in inv["problems"]:
        lines.append(
            f"| `{problem['problem_id']}` | {problem['frame_count']} | "
            f"`{problem['latest_frame_id'] or ''}` | "
            f"{'yes' if problem['imported_bundle_exists'] else 'no'} | "
            f"{'yes' if problem['legacy_lean_proof_exists'] else 'no'} | "
            f"{'yes' if problem['legacy_reconciled'] else 'no'} |"
        )

    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--futon6-root", type=Path, default=DEFAULT_FUTON6_ROOT)
    ap.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    inventory = build_inventory(args.futon6_root.resolve())

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.md_out.parent.mkdir(parents=True, exist_ok=True)

    args.json_out.write_text(json.dumps(inventory, indent=2) + "\n", encoding="utf-8")
    args.md_out.write_text(render_markdown(inventory), encoding="utf-8")

    print(args.json_out)
    print(args.md_out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
