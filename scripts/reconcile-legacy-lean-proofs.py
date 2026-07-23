#!/usr/bin/env python3
"""Reconcile legacy lean-proofs directories into normalized APM bundles.

This pass is intentionally conservative:

- additive only
- no deletion of legacy lean-proofs
- no mutation of futon6
- no claim that legacy lean-proofs supersedes a frame-derived bundle
"""

from __future__ import annotations

import argparse
import json
import shutil
from datetime import datetime, timezone
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROBLEMS_ROOT = REPO_ROOT / "problems"
DEFAULT_LEAN_PROOFS_ROOT = REPO_ROOT / "lean-proofs"
IGNORED_LEAN_PROOF_DIRS = {"worked", "runner-pilot-attempt1", "runner-pilot-attempt2"}


def now_utc() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def maybe_read_text(path: Path) -> str | None:
    if not path.exists():
        return None
    return path.read_text(encoding="utf-8")


def copy_if_exists(src: Path | None, dst: Path) -> bool:
    if src is None or not src.exists():
        return False
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)
    return True


def repo_relative(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT.resolve()))


def count_sorry(text: str | None) -> int:
    if not text:
        return 0
    return text.count("sorry")


def discover_problem_ids(lean_proofs_root: Path) -> list[str]:
    if not lean_proofs_root.exists():
        return []
    return sorted(
        path.name
        for path in lean_proofs_root.iterdir()
        if path.is_dir() and path.name not in IGNORED_LEAN_PROOF_DIRS
    )


def copy_lean_tree(src_root: Path, dst_root: Path) -> list[str]:
    copied: list[str] = []
    for src in sorted(src_root.rglob("*.lean")):
        rel = src.relative_to(src_root)
        dst = dst_root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        copied.append(str(Path("lean") / rel))
    return copied


def collect_sorry_counts(src_root: Path) -> tuple[int, dict[str, int]]:
    counts: dict[str, int] = {}
    total = 0
    for src in sorted(src_root.rglob("*.lean")):
        rel = str(src.relative_to(src_root))
        sorry_count = count_sorry(maybe_read_text(src))
        counts[rel] = sorry_count
        total += sorry_count
    return total, counts


def build_problem_md(problem_id: str, problem_tex_text: str | None, source_rel: str) -> str:
    lines = [
        f"# {problem_id}",
        "",
        "## Bundle Overview",
        "",
        "This directory is the canonical APM problem bundle for this problem.",
        "",
        "This bundle was synthesized from the legacy `lean-proofs/` tree because",
        "no proof-frame bundle existed for this problem at import time.",
        "",
        f"- legacy-source: `{source_rel}`",
        f"- imported-at: `{now_utc()}`",
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


def build_informal_solution_md(problem_id: str, source_rel: str) -> str:
    return "\n".join([
        f"# Informal Solution: {problem_id}",
        "",
        "No worked informal solution was present in the legacy `lean-proofs/` source.",
        "",
        f"Imported source: `{source_rel}`",
        "",
        "Populate this file manually before handing the problem to a human reader",
        "or to LeanDojo if additional mathematical context is needed.",
        "",
    ])


def build_proof_outline_md(problem_id: str, lean_files: list[str], source_rel: str) -> str:
    lines = [
        f"# Proof Outline: {problem_id}",
        "",
        "This proof outline was synthesized from legacy Lean files without a paired",
        "proof-frame workspace.",
        "",
        f"Imported source: `{source_rel}`",
        "",
        "## Imported Lean Files",
        "",
    ]
    for rel in lean_files:
        lines.append(f"- `{rel}`")
    lines.extend([
        "",
        "## Follow-up Needed",
        "",
        "- add a worked informal solution",
        "- extract a formalization plan from the Lean skeleton",
        "- decide whether this legacy attempt should remain canonical",
        "",
    ])
    return "\n".join(lines)


def build_archive_readme(problem_id: str, source_rel: str, lean_files: list[str]) -> str:
    lines = [
        f"# Historical Legacy Lean: {problem_id}",
        "",
        "This directory preserves the pre-frame `lean-proofs/` material for",
        "comparison and salvage.",
        "",
        f"- imported-source: `{source_rel}`",
        f"- imported-at: `{now_utc()}`",
        "",
        "This is archival material, not the canonical bundle winner.",
        "",
        "## Lean Files",
        "",
    ]
    for rel in lean_files:
        lines.append(f"- `{rel}`")
    return "\n".join(lines) + "\n"


def append_historical_source(problem_root: Path, archive_root: Path) -> None:
    status_path = problem_root / "status.json"
    if not status_path.exists():
        return
    status = read_json(status_path)
    sources = status.setdefault("historical_sources", [])
    entry = {
        "kind": "legacy-lean-proofs",
        "path": repo_relative(archive_root),
    }
    if entry not in sources:
        sources.append(entry)
        write_text(status_path, json.dumps(status, indent=2) + "\n")


def is_legacy_only_bundle(problem_root: Path) -> bool:
    status_path = problem_root / "status.json"
    if not status_path.exists():
        return False
    try:
        status = read_json(status_path)
    except json.JSONDecodeError:
        return False
    return (
        status.get("schema") == "apm-problem-bundle.v1"
        and status.get("source", {}).get("kind") == "legacy-lean-proofs"
        and not (problem_root / "candidates").exists()
    )


def import_legacy_only(problem_id: str, legacy_root: Path, problem_root: Path, force: bool) -> str:
    if problem_root.exists() and any(problem_root.iterdir()) and not force:
        raise SystemExit(f"bundle exists: {problem_root} (use --force to overwrite)")
    if force and problem_root.exists():
        shutil.rmtree(problem_root)

    problem_tex_src = REPO_ROOT / "apm" / f"{problem_id}.tex"
    if not problem_tex_src.exists():
        problem_tex_src = None

    problem_root.mkdir(parents=True, exist_ok=True)
    lean_files = copy_lean_tree(legacy_root, problem_root / "lean")
    total_sorry, sorry_by_file = collect_sorry_counts(legacy_root)
    problem_tex_text = maybe_read_text(problem_tex_src) if problem_tex_src else None
    source_rel = repo_relative(legacy_root)
    copied_problem_tex = copy_if_exists(problem_tex_src, problem_root / "problem.tex")

    write_text(problem_root / "problem.md", build_problem_md(problem_id, problem_tex_text, source_rel))
    write_text(problem_root / "informal-solution.md", build_informal_solution_md(problem_id, source_rel))
    write_text(problem_root / "proof-outline.md", build_proof_outline_md(problem_id, lean_files, source_rel))

    main_rel = "lean/Main.lean" if (problem_root / "lean" / "Main.lean").exists() else (lean_files[0] if lean_files else None)
    status = {
        "schema": "apm-problem-bundle.v1",
        "problem_id": problem_id,
        "bundle_root": repo_relative(problem_root),
        "layout": "single-bundle",
        "source": {
            "kind": "legacy-lean-proofs",
            "legacy_lean_root": str(legacy_root.resolve()),
            "problem_tex": str(problem_tex_src.resolve()) if problem_tex_src else None,
        },
        "lean": {
            "main": main_rel,
            "scratch": None,
            "files": lean_files,
            "sorry_count_main": sorry_by_file.get("Main.lean", 0),
            "sorry_count_scratch": 0,
            "sorry_count_total": total_sorry,
            "sorry_count_by_file": sorry_by_file,
        },
        "artifacts": {
            "has_problem_tex": copied_problem_tex,
            "has_problem_md": True,
            "has_informal_solution": True,
            "has_proof_outline": True,
            "has_proof_plan": False,
            "has_changelog": False,
            "has_workspace_metadata": False,
            "has_receipt": False,
        },
        "classification": "partial" if total_sorry > 0 else "complete",
        "imported_at": now_utc(),
    }
    write_text(problem_root / "status.json", json.dumps(status, indent=2) + "\n")
    return f"[created-bundle] {problem_id}"


def archive_overlap(problem_id: str, legacy_root: Path, problem_root: Path, force: bool) -> str:
    archive_root = problem_root / "historical" / "legacy-lean-proofs"
    if archive_root.exists() and not force:
        raise SystemExit(f"archive exists: {archive_root} (use --force to overwrite)")
    if force and archive_root.exists():
        shutil.rmtree(archive_root)

    problem_tex_src = REPO_ROOT / "apm" / f"{problem_id}.tex"
    if not problem_tex_src.exists():
        problem_tex_src = None

    archive_root.mkdir(parents=True, exist_ok=True)
    lean_files = copy_lean_tree(legacy_root, archive_root / "lean")
    total_sorry, sorry_by_file = collect_sorry_counts(legacy_root)
    source_rel = repo_relative(legacy_root)
    copied_problem_tex = copy_if_exists(problem_tex_src, archive_root / "problem.tex")

    write_text(archive_root / "README.md", build_archive_readme(problem_id, source_rel, lean_files))
    archive_status = {
        "schema": "apm-problem-legacy-archive.v1",
        "problem_id": problem_id,
        "archive_root": repo_relative(archive_root),
        "source": {
            "kind": "legacy-lean-proofs",
            "legacy_lean_root": str(legacy_root.resolve()),
            "problem_tex": str(problem_tex_src.resolve()) if problem_tex_src else None,
        },
        "lean": {
            "files": lean_files,
            "sorry_count_total": total_sorry,
            "sorry_count_by_file": sorry_by_file,
        },
        "artifacts": {
            "has_problem_tex": copied_problem_tex,
            "has_readme": True,
        },
        "imported_at": now_utc(),
    }
    write_text(archive_root / "status.json", json.dumps(archive_status, indent=2) + "\n")
    append_historical_source(problem_root, archive_root)
    return f"[archived-overlap] {problem_id}"


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--problem-id", action="append",
                    help="Restrict reconciliation to one or more problem ids")
    ap.add_argument("--problems-root", type=Path, default=DEFAULT_PROBLEMS_ROOT)
    ap.add_argument("--lean-proofs-root", type=Path, default=DEFAULT_LEAN_PROOFS_ROOT)
    ap.add_argument("--force", action="store_true",
                    help="Overwrite previously imported legacy outputs")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    lean_proofs_root = args.lean_proofs_root.resolve()
    problems_root = args.problems_root.resolve()
    problem_ids = args.problem_id or discover_problem_ids(lean_proofs_root)

    created = 0
    archived = 0
    for problem_id in problem_ids:
        legacy_root = lean_proofs_root / problem_id
        if not legacy_root.exists():
            raise SystemExit(f"missing legacy lean root: {legacy_root}")
        problem_root = problems_root / problem_id
        if problem_root.exists() and not is_legacy_only_bundle(problem_root):
            print(archive_overlap(problem_id, legacy_root, problem_root, args.force))
            archived += 1
        else:
            print(import_legacy_only(problem_id, legacy_root, problem_root, args.force))
            created += 1

    print(f"created={created} archived={archived} total={len(problem_ids)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
