#!/usr/bin/env python3
"""Import one existing APM proof frame into a self-contained apm-lean bundle.

This is a first-pass migration tool. It is intentionally conservative:

- additive only
- no mutation of futon6 state
- no mutation of legacy apm-lean frame locations
- no attempt to pick winners among multiple competing frames
"""

from __future__ import annotations

import argparse
import json
import shutil
from datetime import datetime, timezone
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROBLEMS_ROOT = REPO_ROOT / "problems"
DEFAULT_FUTON6_ROOT = REPO_ROOT.parent / "futon6"


def now_utc() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def maybe_read_text(path: Path) -> str | None:
    if not path.exists():
        return None
    return path.read_text(encoding="utf-8")


def count_sorry(text: str | None) -> int:
    if not text:
        return 0
    return text.count("sorry")


def repo_relative(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT.resolve()))


def discover_problem_frames(futon6_root: Path, problem_id: str) -> list[dict]:
    proof_frames_root = futon6_root / ".state" / "proof-frames" / problem_id
    records: list[dict] = []
    if not proof_frames_root.exists():
        return records

    for workspace_json in sorted(proof_frames_root.glob("*/workspace.json")):
        metadata = read_json(workspace_json)
        records.append({
            "frame_id": metadata.get("frame/id"),
            "generated_at": metadata.get("workspace/generated-at"),
            "workspace_json": str(workspace_json.resolve()),
        })
    return records


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


def infer_receipt_path(workspace_metadata_path: Path, metadata: dict) -> Path | None:
    frame_id = metadata.get("frame/id")
    problem_id = metadata.get("proof/problem-id")
    if not frame_id or not problem_id:
        return None
    candidate = workspace_metadata_path.parent.parent / f"{frame_id}.json"
    return candidate if candidate.exists() else None


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def copy_if_exists(src: Path | None, dst: Path) -> bool:
    if src is None or not src.exists():
        return False
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)
    return True


def build_problem_md(problem_id: str, problem_tex_text: str | None, metadata: dict) -> str:
    lines = [
        f"# {problem_id}",
        "",
        "## Bundle Overview",
        "",
        "This directory is the canonical APM problem bundle for this problem.",
        "",
        "Contents:",
        "- `problem.tex`: raw problem source when available",
        "- `informal-solution.md`: best-effort worked mathematical solution",
        "- `proof-outline.md`: formalization-oriented outline and blockers",
        "- `lean/Main.lean`: current Lean development",
        "- `status.json`: machine-readable bundle status",
        "",
        "## Imported Provenance",
        "",
        f"- imported-at: `{now_utc()}`",
        f"- source-frame-id: `{metadata.get('frame/id', '')}`",
        f"- source-module-root: `{metadata.get('frame/module-root', '')}`",
        "",
        "## Problem Statement",
        "",
    ]
    if problem_tex_text:
        lines.extend([
            "Raw TeX source:",
            "",
            "```tex",
            problem_tex_text.rstrip(),
            "```",
        ])
    else:
        lines.extend([
            "Problem TeX source was not found during import.",
            "",
            "Populate this file manually if a better problem statement rendering is needed.",
        ])
    return "\n".join(lines) + "\n"


def build_candidate_readme(problem_id: str, frame_records: list[dict]) -> str:
    latest = choose_latest_frame(frame_records)
    lines = [
        f"# {problem_id}",
        "",
        "This problem currently has multiple imported historical proof frames.",
        "",
        "During migration, each frame is preserved as its own candidate bundle under:",
        "",
        f"- `problems/{problem_id}/candidates/<frame-id>/`",
        "",
        f"Candidate count: `{len(frame_records)}`",
        f"Recommended latest frame: `{latest['frame_id'] if latest else ''}`",
        "",
        "No canonical winner has been selected yet.",
        "",
        "## Candidates",
        "",
    ]
    for rec in sorted(frame_records, key=lambda r: (r.get("generated_at") or "", r.get("frame_id") or "")):
        lines.append(
            f"- `{rec.get('frame_id')}`"
            + (f" (`{rec.get('generated_at')}`)" if rec.get("generated_at") else "")
        )
    return "\n".join(lines) + "\n"


def build_informal_solution_md(execute_text: str | None, problem_id: str) -> str:
    lines = [
        f"# Informal Solution: {problem_id}",
        "",
        "This file is the best available worked mathematical solution imported",
        "from the historical proof-frame workspace.",
        "",
    ]
    if execute_text:
        lines.append(execute_text.rstrip())
    else:
        lines.extend([
            "No `execute.md` was available during import.",
            "",
            "Populate this file manually from the best available mathematical writeup.",
        ])
    return "\n".join(lines) + "\n"


def build_proof_outline_md(
    execute_text: str | None,
    proof_plan_text: str | None,
    changelog_text: str | None,
    problem_id: str,
) -> str:
    lines = [
        f"# Proof Outline: {problem_id}",
        "",
        "This file packages the formalization-oriented context that should travel",
        "with the Lean files.",
        "",
        "## Notes",
        "",
        "The content below was imported automatically and may need cleanup.",
        "",
    ]

    if proof_plan_text:
        lines.extend([
            "## Imported Proof Plan",
            "",
            "```clojure",
            proof_plan_text.rstrip(),
            "```",
            "",
        ])

    if changelog_text:
        lines.extend([
            "## Imported Changelog",
            "",
            "```clojure",
            changelog_text.rstrip(),
            "```",
            "",
        ])

    if execute_text:
        lines.extend([
            "## Imported Execution Notes",
            "",
            execute_text.rstrip(),
        ])
    else:
        lines.extend([
            "No `execute.md` was available during import.",
        ])

    return "\n".join(lines) + "\n"


def build_candidate_status(problem_id: str, problem_root: Path, frame_records: list[dict]) -> dict:
    latest = choose_latest_frame(frame_records)
    return {
        "schema": "apm-problem-candidate-set.v1",
        "problem_id": problem_id,
        "bundle_root": repo_relative(problem_root),
        "layout": "candidate-set",
        "candidate_count": len(frame_records),
        "frame_ids": [rec["frame_id"] for rec in frame_records if rec.get("frame_id")],
        "recommended_latest_frame_id": latest["frame_id"] if latest else None,
        "selected_frame_id": None,
        "imported_at": now_utc(),
    }


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("workspace_metadata", type=Path,
                    help="Path to futon6 proof-frame workspace.json")
    ap.add_argument("--receipt", type=Path,
                    help="Optional path to the sibling proof-frame receipt JSON")
    ap.add_argument("--problems-root", type=Path, default=DEFAULT_PROBLEMS_ROOT)
    ap.add_argument("--futon6-root", type=Path, default=DEFAULT_FUTON6_ROOT)
    ap.add_argument("--force", action="store_true",
                    help="Overwrite an existing bundle directory")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    workspace_metadata_path = args.workspace_metadata.resolve()
    metadata = read_json(workspace_metadata_path)

    problem_id = metadata["proof/problem-id"]
    frame_id = metadata["frame/id"]
    problem_root = args.problems_root.resolve() / problem_id
    frame_records = discover_problem_frames(args.futon6_root.resolve(), problem_id)
    duplicate_mode = len(frame_records) > 1
    bundle_root = (
        problem_root / "candidates" / frame_id
        if duplicate_mode
        else problem_root
    )

    if bundle_root.exists() and not args.force:
        raise SystemExit(f"bundle exists: {bundle_root} (use --force to overwrite)")

    if args.force and bundle_root.exists():
        shutil.rmtree(bundle_root)

    artifacts = metadata.get("artifacts", {})
    lean_main_src = Path(artifacts["lean-main"]).resolve()
    lean_scratch_src = Path(artifacts["lean-scratch"]).resolve()
    proof_plan_src = Path(artifacts["proof-plan"]).resolve()
    changelog_src = Path(artifacts["changelog"]).resolve()
    execute_src = Path(artifacts["execute-notes"]).resolve()

    receipt_src = args.receipt.resolve() if args.receipt else infer_receipt_path(workspace_metadata_path, metadata)
    problem_tex_src = (REPO_ROOT / "apm" / f"{problem_id}.tex").resolve()
    if not problem_tex_src.exists():
        problem_tex_src = None

    bundle_root.mkdir(parents=True, exist_ok=True)

    copied_problem_tex = copy_if_exists(problem_tex_src, bundle_root / "problem.tex")
    copied_proof_plan = copy_if_exists(proof_plan_src, bundle_root / "proof-plan.edn")
    copied_changelog = copy_if_exists(changelog_src, bundle_root / "changelog.edn")
    copied_workspace = copy_if_exists(workspace_metadata_path, bundle_root / "workspace.json")
    copied_receipt = copy_if_exists(receipt_src, bundle_root / "receipt.json")
    copied_main = copy_if_exists(lean_main_src, bundle_root / "lean" / "Main.lean")
    copied_scratch = copy_if_exists(lean_scratch_src, bundle_root / "lean" / "Scratch.lean")

    problem_tex_text = maybe_read_text(problem_tex_src) if problem_tex_src else None
    execute_text = maybe_read_text(execute_src)
    proof_plan_text = maybe_read_text(proof_plan_src)
    changelog_text = maybe_read_text(changelog_src)
    lean_main_text = maybe_read_text(lean_main_src)
    lean_scratch_text = maybe_read_text(lean_scratch_src)

    write_text(bundle_root / "problem.md", build_problem_md(problem_id, problem_tex_text, metadata))
    write_text(bundle_root / "informal-solution.md", build_informal_solution_md(execute_text, problem_id))
    write_text(
        bundle_root / "proof-outline.md",
        build_proof_outline_md(execute_text, proof_plan_text, changelog_text, problem_id),
    )

    if duplicate_mode:
        write_text(problem_root / "README.md", build_candidate_readme(problem_id, frame_records))
        write_text(
            problem_root / "status.json",
            json.dumps(build_candidate_status(problem_id, problem_root, frame_records), indent=2) + "\n",
        )

    status = {
        "schema": "apm-problem-bundle.v1",
        "problem_id": problem_id,
        "bundle_root": repo_relative(bundle_root),
        "layout": "candidate" if duplicate_mode else "single-bundle",
        "source": {
            "workspace_metadata": str(workspace_metadata_path),
            "receipt": str(receipt_src) if receipt_src else None,
            "problem_tex": str(problem_tex_src) if problem_tex_src else None,
            "frame_id": frame_id,
            "module_root": metadata.get("frame/module-root"),
        },
        "lean": {
            "main": "lean/Main.lean" if copied_main else None,
            "scratch": "lean/Scratch.lean" if copied_scratch else None,
            "sorry_count_main": count_sorry(lean_main_text),
            "sorry_count_scratch": count_sorry(lean_scratch_text),
            "sorry_count_total": count_sorry(lean_main_text) + count_sorry(lean_scratch_text),
        },
        "artifacts": {
            "has_problem_tex": copied_problem_tex,
            "has_problem_md": True,
            "has_informal_solution": True,
            "has_proof_outline": True,
            "has_proof_plan": copied_proof_plan,
            "has_changelog": copied_changelog,
            "has_workspace_metadata": copied_workspace,
            "has_receipt": copied_receipt,
        },
        "classification": "partial" if count_sorry(lean_main_text) + count_sorry(lean_scratch_text) > 0 else "complete",
        "imported_at": now_utc(),
    }
    write_text(bundle_root / "status.json", json.dumps(status, indent=2) + "\n")

    print(bundle_root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
