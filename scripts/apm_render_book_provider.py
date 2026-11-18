#!/usr/bin/env python3
"""APM's filesystem-backed adapters for mfuton's render-book seams.

No proof graph is involved.  The declaration provider delegates parsing to the
typed entity surface distributed with mfuton-share.  The arrangement exporter
uses the operator's id list as the book order: one problem/page per id, and the
declarations in each ``Main.lean`` remain in source order.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from leanfile import docstring, segment


@dataclass(frozen=True)
class ApmSection:
    id: str
    lean_files: tuple[PurePosixPath, ...]


class ApmBookDeclarationProvider:
    """Implementation of mfuton's ``BookDeclarationProvider`` protocol.

    APM already has a deliberately small top-level Lean segmenter used by its
    proof publisher.  Turning those segments into mfuton's typed declaration
    carriers keeps this adapter self-contained and avoids requiring Rob's
    proof graph or private vendored tree-sitter grammar.
    """

    def build(self, *, repo_root: Path, project_root: Path, paths: Sequence[PurePosixPath]):
        from mfuton.lean.lean_blueprint_book.book_declaration_source import (
            BookDeclarations,
            BookModuleDeclarations,
        )
        from mfuton.lean.entity_surface.nodes.leaves import (
            LeanAbbrev,
            LeanClass,
            LeanDefinition,
            LeanGenericDeclaration,
            LeanInductive,
            LeanInstance,
            LeanLemma,
            LeanStructure,
            LeanTheorem,
        )

        declaration_types = {
            "theorem": LeanTheorem,
            "lemma": LeanLemma,
            "def": LeanDefinition,
            "abbrev": LeanAbbrev,
            "instance": LeanInstance,
            "structure": LeanStructure,
            "class": LeanClass,
            "inductive": LeanInductive,
        }
        modules: list[BookModuleDeclarations] = []
        for rel in paths:
            source = repo_root / rel
            candidates = sorted(source.rglob("*.lean")) if source.is_dir() else [source]
            for lean_file in candidates:
                if not lean_file.is_file():
                    continue
                source_lines = lean_file.read_text(encoding="utf-8").splitlines()
                declarations = []
                cursor = 0
                for chunk in segment(source_lines):
                    span = len(chunk["lines"])
                    start = cursor + 1
                    cursor += span
                    if not chunk["name"]:
                        continue
                    declaration_type = declaration_types.get(chunk["kind"], LeanGenericDeclaration)
                    text = "\n".join(chunk["lines"])
                    declarations.append(
                        declaration_type(
                            name=chunk["name"],
                            full_name=chunk["name"],
                            file=str(lean_file),
                            start_line=start,
                            end_line=cursor,
                            text=text,
                            docstring=docstring(chunk) or "",
                            raw_lines=list(chunk["lines"]),
                            code_lines=list(chunk["lines"]),
                            source_system="apm-leanfile",
                            source_artifact=str(lean_file),
                        )
                    )
                module_name = ".".join(lean_file.relative_to(project_root).with_suffix("").parts)
                modules.append(BookModuleDeclarations(full_name=module_name, declarations=tuple(declarations)))
        return BookDeclarations(
            modules=tuple(modules)
        )


def install() -> ApmBookDeclarationProvider:
    """Install and return APM's provider in the current render-book process."""
    from mfuton.lean.lean_blueprint_book.book_declaration_source import set_book_declaration_provider

    provider = ApmBookDeclarationProvider()
    set_book_declaration_provider(provider)
    return provider


def arrange(repo_root: Path, ids: Sequence[str]) -> tuple[ApmSection, ...]:
    sections: list[ApmSection] = []
    for problem_id in ids:
        rel = PurePosixPath("problems") / problem_id / "lean" / "Main.lean"
        if (repo_root / rel).is_file():
            sections.append(ApmSection(problem_id, (rel,)))
    return tuple(sections)


def arrangement_json(repo_root: Path, ids: Sequence[str]) -> dict[str, object]:
    sections = arrange(repo_root, ids)
    return {
        "version": 1,
        "provider": "apm-filesystem",
        "repo_root": str(repo_root.resolve()),
        "sections": [
            {"id": section.id, "lean_files": [path.as_posix() for path in section.lean_files]}
            for section in sections
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("id_list", type=Path)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    ids = [item for item in args.id_list.read_text(encoding="utf-8").split() if item]
    payload = arrangement_json(args.repo_root, ids)
    rendered = json.dumps(payload, indent=2) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
