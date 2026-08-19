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

NEXT_AREAS = {
    "a93A02": [], "a96A08": [], "a99J03": [], "m95A02": [], "aunk04": [],
    "m93A02": [], "m93J02": [], "t94J07": ["differential-forms"],
    "m00A03": [], "m99A01": [], "m00A02": [], "b94J01": [], "b96A02": [],
    "b98J04": [], "m01J06": [], "t96J08": ["differential-forms"],
    "m95J03": [], "a97A02": [], "m98A05": [], "m00A04": [], "m98A03": [],
    "m94J04": ["differential-forms"], "t92J05": ["fundamental-group"],
    "t00J07": [],
    "t97A03": ["covering-space", "fundamental-group", "singular-homology"],
    "m95J01": [], "t01A02": ["covering-space", "singular-homology"],
    "m93A04": [], "t97J05": [], "t01J01": ["singular-homology"],
}

ADVERSARIAL_AREAS = {
    "m98J02": [],
    "t01A05": ["covering-space", "singular-homology"],
    "t94J05": ["transversality"],
    "t94A09": [], "t91J03": [],
    "t91A08": ["degree-theory"],
    "t03J05": ["intersection-theory"],
    "t95J04": ["covering-space", "singular-homology", "transversality"],
    "t03J06": ["differential-forms", "stokes"],
    "t98A03": ["covering-space", "fundamental-group"],
    "t01A03": ["singular-homology"],
    "a98A07": [], "m98J04": [], "m94A03": [], "a98J03": [],
    # Three sufficient routes to the same transform evaluation.
    "a03J05": ["complex-analysis", "fourier-analysis", "measure-integral"],
    "m02A02": [], "t96J05": ["transversality"],
    "t94A07": ["singular-homology"],
    "a01J06": [], "t95J05": [], "m96A06": [], "m97A04": [],
    "t94A10": ["differential-forms", "stokes"],
    "a98A04": [], "a92J01": [], "m97A03": [],
    "t97A04": ["singular-homology"],
    "t00A02": ["covering-space", "orientation"],
    "m94A04": [],
}

AMBIGUOUS = {"a96A08", "a99J03", "t00J07", "t97J05"}
ALTERNATIVES = {"a03J05"}

LEGACY_FIELDS = ("closer_hop", "boundary", "closer_note", "sorry_details", "closer_progress")
RESOLVED_CLASSIFICATIONS = {"complete", "compiled", "closed", "proved", "solved"}


def main() -> None:
    repo = Path(__file__).resolve().parents[1]
    # Backfill the discriminator on every structured record, including records
    # authored before this migration. t97J06 explicitly names alternative
    # witnesses; all other existing records describe jointly required pieces.
    for path in (repo / "problems").glob("*/status.json"):
        status = json.loads(path.read_text())
        changed = False
        for item in status.get("obstructions", []):
            if "areas_are" not in item:
                item["areas_are"] = ("alternatives" if path.parent.name == "t97J06"
                                     and item.get("frame") == "phase-2b-legacy-migration"
                                     else "necessary")
                changed = True
        if changed:
            path.write_text(json.dumps(status, indent=2) + "\n")

    for problem_id, areas in (AREAS | NEXT_AREAS | ADVERSARIAL_AREAS).items():
        path = repo / "problems" / problem_id / "status.json"
        status = json.loads(path.read_text())
        existing = status.get("obstructions", [])
        frame = ("phase-2d-adversarial-migration" if problem_id in ADVERSARIAL_AREAS
                 else "phase-2c-legacy-migration" if problem_id in NEXT_AREAS
                 else "phase-2b-legacy-migration")
        if any(item.get("frame") == frame for item in existing):
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
            "areas_are": ("ambiguous" if problem_id in AMBIGUOUS else
                          "alternatives" if problem_id in ALTERNATIVES else "necessary"),
            "missing": "\n\n".join(paragraphs),
            "recorded_by": "codex-6",
            "frame": frame,
            "at_commit": "a00ea1f",
            "date": "2026-08-19",
            "resolved": resolved,
        }
        status["obstructions"] = existing + [entry]
        path.write_text(json.dumps(status, indent=2) + "\n")
        print(problem_id)


if __name__ == "__main__":
    main()
