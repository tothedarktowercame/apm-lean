#!/usr/bin/env python3
"""Import harvested APM informal proofs into canonical problem bundles.

The import is additive and conservative:

- existing ``problems/<id>/informal-solution.md`` files are never overwritten
- existing problem bundles keep their current status files
- newly created problem roots get enough bundle metadata to stand alone
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
from datetime import datetime, timezone
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROBLEMS_ROOT = REPO_ROOT / "problems"
DEFAULT_APM_SOURCE_ROOT = REPO_ROOT / "apm"
DEFAULT_HARVEST_ROOT = Path("/home/joe/code/futon3c/data/apm-informal-proofs")
APM_HEADING_RE = re.compile(r"^# APM\s+([A-Za-z0-9]+)", re.MULTILINE)


def now_utc() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def repo_relative(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT.resolve()))


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def copy_if_missing(src: Path, dst: Path) -> bool:
    if not src.exists() or dst.exists():
        return False
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)
    return True


def problem_id_from_harvest(path: Path) -> str:
    name = path.stem
    if not name.startswith("apm-"):
        raise ValueError(f"unexpected harvest filename: {path}")
    return name.removeprefix("apm-")


def validate_harvest_identity(harvest_path: Path, problem_id: str) -> None:
    """Reject a harvested proof whose own APM heading names another problem."""
    text = harvest_path.read_text(encoding="utf-8")
    heading = APM_HEADING_RE.search(text)
    if heading and heading.group(1) != problem_id:
        raise ValueError(
            f"harvest identity mismatch: {harvest_path.name} claims "
            f"{heading.group(1)}, expected {problem_id}"
        )


def build_problem_md(problem_id: str, problem_tex_text: str | None, harvest_name: str) -> str:
    lines = [
        f"# {problem_id}",
        "",
        "## Bundle Overview",
        "",
        "This directory is the canonical APM problem bundle for this problem.",
        "",
        "The informal solution was imported from the harvested APM informal-proof",
        "corpus.",
        "",
        "- informal-solution: `informal-solution.md`",
        f"- harvested-filename: `{harvest_name}`",
        f"- imported-at: `{now_utc()}`",
        "",
        "## Problem Statement",
        "",
    ]
    if problem_tex_text:
        lines.extend(
            [
                "Raw TeX source:",
                "",
                "```tex",
                problem_tex_text.rstrip(),
                "```",
            ]
        )
    else:
        lines.extend(
            [
                "Problem TeX source was not found during import.",
                "",
                "Populate this file manually if a better problem statement rendering is needed.",
            ]
        )
    return "\n".join(lines) + "\n"


def build_proof_outline_md(problem_id: str, harvest_name: str) -> str:
    return "\n".join(
        [
            f"# Proof Outline: {problem_id}",
            "",
            "This bundle currently has a harvested informal solution but no imported",
            "Lean proof attempt in this problem root.",
            "",
            "- informal-solution: `informal-solution.md`",
            f"- harvested-filename: `{harvest_name}`",
            "",
            "## Follow-up Needed",
            "",
            "- extract a formalization-oriented proof outline from the informal solution",
            "- add or select the canonical Lean attempt for this problem",
            "",
        ]
    )


def import_one(harvest_path: Path, args: argparse.Namespace) -> str:
    problem_id = problem_id_from_harvest(harvest_path)
    validate_harvest_identity(harvest_path, problem_id)
    problem_tex_src = args.apm_source_root / f"{problem_id}.tex"
    if not problem_tex_src.exists():
        return f"[skip-no-source] {problem_id}"

    problem_root = args.problems_root / problem_id
    informal_dst = problem_root / "informal-solution.md"
    if informal_dst.exists():
        return f"[skip-existing] {problem_id}"

    problem_root.mkdir(parents=True, exist_ok=True)
    shutil.copy2(harvest_path, informal_dst)

    copied_problem_tex = copy_if_missing(problem_tex_src, problem_root / "problem.tex")
    harvest_name = harvest_path.name
    problem_tex_text = problem_tex_src.read_text(encoding="utf-8") if problem_tex_src.exists() else None

    if not (problem_root / "problem.md").exists():
        write_text(problem_root / "problem.md", build_problem_md(problem_id, problem_tex_text, harvest_name))
    if not (problem_root / "proof-outline.md").exists():
        write_text(problem_root / "proof-outline.md", build_proof_outline_md(problem_id, harvest_name))
    if not (problem_root / "status.json").exists():
        status = {
            "schema": "apm-problem-bundle.v1",
            "problem_id": problem_id,
            "bundle_root": repo_relative(problem_root),
            "layout": "single-bundle",
            "source": {
                "kind": "harvested-informal-proof",
                "informal_solution": "informal-solution.md",
                "harvested_filename": harvest_name,
                "problem_tex": repo_relative(problem_tex_src),
            },
            "lean": {
                "main": None,
                "scratch": None,
                "files": [],
                "sorry_count_main": 0,
                "sorry_count_scratch": 0,
                "sorry_count_total": 0,
            },
            "artifacts": {
                "has_problem_tex": copied_problem_tex or (problem_root / "problem.tex").exists(),
                "has_problem_md": True,
                "has_informal_solution": True,
                "has_proof_outline": True,
                "has_proof_plan": False,
                "has_changelog": False,
                "has_workspace_metadata": False,
                "has_receipt": False,
            },
            "classification": "informal-only",
            "imported_at": now_utc(),
        }
        write_text(problem_root / "status.json", json.dumps(status, indent=2) + "\n")

    return f"[imported] {problem_id}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--harvest-root", type=Path, default=DEFAULT_HARVEST_ROOT)
    parser.add_argument("--problems-root", type=Path, default=DEFAULT_PROBLEMS_ROOT)
    parser.add_argument("--apm-source-root", type=Path, default=DEFAULT_APM_SOURCE_ROOT)
    args = parser.parse_args()

    imported = 0
    skipped = 0
    for harvest_path in sorted(args.harvest_root.glob("apm-*.md")):
        result = import_one(harvest_path, args)
        print(result)
        if result.startswith("[imported]"):
            imported += 1
        else:
            skipped += 1
    print(f"imported={imported} skipped={skipped}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
