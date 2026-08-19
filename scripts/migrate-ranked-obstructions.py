#!/usr/bin/env python3
"""Install the hand-adjudicated phase-2b legacy obstruction migration.

The area sets below were assigned after reading every contributing legacy
record. Prose is copied from its original fields at execution time so the
structured record preserves evidence rather than replacing it with tags.
"""

from __future__ import annotations

import json
from pathlib import Path


AREAS = {
    "m94A01": [],
    "t00A01": ["mayer-vietoris", "van-kampen"],
    "t00J02": ["singular-homology", "transversality"],
    "t01A04": ["covering-space", "fundamental-group", "singular-homology"],
    "t01J03": ["fundamental-group", "mayer-vietoris", "singular-homology", "van-kampen"],
    "t02A03": ["fundamental-group", "singular-homology"],
    "t02A04": ["singular-homology"],
    "t02A07": ["transversality"],
    "t02A08": ["orientation", "singular-homology"],
    "t03J01": ["cohomology", "singular-homology"],
    "t03J02": ["fundamental-group", "mayer-vietoris", "singular-homology", "van-kampen"],
    "t03J03": ["covering-space", "fundamental-group", "orientation"],
    "t91A05": ["fundamental-group"],
    "t91J02": ["fundamental-group"],
    "t92J06": ["covering-space"],
    "t93A03": ["fundamental-group", "van-kampen"],
    "t93A04": ["transversality"],
    "t94A06": ["transversality"],
    "t94J04": ["covering-space", "fundamental-group", "orientation"],
    "t94J08": ["orientation", "singular-homology"],
    "t94J09": ["singular-homology"],
    "t95J03": [],
    "t95J06": ["covering-space", "orientation"],
    "t96A03": ["cellular-homology", "mayer-vietoris", "singular-homology"],
    "t96J06": ["intersection-theory", "kunneth", "singular-homology"],
    "t97A01": ["cellular-homology", "fundamental-group", "singular-homology", "van-kampen"],
    "t97A02": ["cohomology", "singular-homology"],
    "t97J02": ["covering-space", "orientation"],
    "t97J03": ["fundamental-group"],
    "t97J04": ["fundamental-group", "mayer-vietoris", "singular-homology", "van-kampen"],
    # The current blocker is Circle noncontractibility. The prose lists degree,
    # pi1, and H1 as alternative witnesses; no one area is required.
    "t97J06": [],
    "t98A01": ["covering-space"],
    "t98A02": ["cellular-homology", "excision", "mayer-vietoris", "orientation",
                "singular-homology"],
    "t99J03": ["orientation"],
}

LEGACY_FIELDS = ("closer_hop", "boundary", "closer_note", "sorry_details", "closer_progress")
RESOLVED_CLASSIFICATIONS = {"complete", "compiled", "closed", "proved", "solved"}


def main() -> None:
    repo = Path(__file__).resolve().parents[1]
    for problem_id, areas in AREAS.items():
        path = repo / "problems" / problem_id / "status.json"
        status = json.loads(path.read_text())
        existing = status.get("obstructions", [])
        if any(item.get("frame") == "phase-2b-legacy-migration" for item in existing):
            path.write_text(json.dumps(status, indent=2) + "\n")
            continue
        paragraphs = []
        for field in LEGACY_FIELDS:
            value = status.get(field)
            if value is not None:
                rendered = value if isinstance(value, str) else json.dumps(value, sort_keys=True)
                paragraphs.append(f"[{field}] {rendered}")
        resolved = None
        if status.get("classification") in RESOLVED_CLASSIFICATIONS:
            resolved = {"by": "bundle classification records the work closed",
                        "date": "2026-08-19", "at_commit": "a00ea1f"}
        entry = {
            "areas": areas,
            "missing": "\n\n".join(paragraphs),
            "recorded_by": "codex-6",
            "frame": "phase-2b-legacy-migration",
            "at_commit": "a00ea1f",
            "date": "2026-08-19",
            "resolved": resolved,
        }
        status["obstructions"] = existing + [entry]
        path.write_text(json.dumps(status, indent=2) + "\n")
        print(problem_id)


if __name__ == "__main__":
    main()
