#!/usr/bin/env python3
"""Cluster normalized proved lemma signatures across completed APM bundles."""

from __future__ import annotations

import json
import re
from collections import defaultdict
from pathlib import Path

DONE = {"complete", "proved", "solved", "complete-lean-proof", "closed", "compiled"}
ROW = re.compile(r"^\| `([^`]+)` \| ([^|]+) \| `(.*)` \|$")
TOKEN = re.compile(r"(?<![\w'])[^\W\d][\w']*(?![\w'])", re.UNICODE)
BINDER = re.compile(r"([({])([^:(){}]+?)\s*:\s*([^(){}]+)([)}])")
LOCAL_PREFIX = re.compile(r"(?i)\bapm[_A-Za-z]*[a-z]\d{2}[aj]\d{2}_")


def normalize(signature: str) -> str:
    """Normalize surface syntax conservatively; no theorem proving is implied."""
    text = signature.replace(" ", " ")
    env: dict[str, str] = {}
    next_id = 0

    def binder(match: re.Match[str]) -> str:
        nonlocal next_id
        opening, names, typ, closing = match.groups()
        renamed = []
        for name in names.split():
            if TOKEN.fullmatch(name) and name not in {"_"}:
                replacement = env.get(name)
                if replacement is None:
                    replacement = f"v{next_id}"
                    next_id += 1
                    env[name] = replacement
                renamed.append(replacement)
            else:
                renamed.append(name)
        return f"{opening}{' '.join(renamed)}:{typ}{closing}"

    # Binder types may mention earlier binders, so apply prior substitutions first.
    pieces = []
    pos = 0
    for match in BINDER.finditer(text):
        prefix = text[pos:match.start()]
        for old, new in env.items():
            prefix = re.sub(rf"(?<![\w']){re.escape(old)}(?![\w'])", new, prefix)
        pieces.append(prefix)
        rendered = binder(match)
        for old, new in env.items():
            rendered = re.sub(rf"(?<![\w']){re.escape(old)}(?![\w'])", new, rendered)
        pieces.append(rendered)
        pos = match.end()
    tail = text[pos:]
    for old, new in env.items():
        tail = re.sub(rf"(?<![\w']){re.escape(old)}(?![\w'])", new, tail)
    text = "".join(pieces) + tail
    text = LOCAL_PREFIX.sub("apm_local_", text)
    # Namespace qualification is irrelevant for this lexical comparison. Retain
    # the basename, including projection-like chains' final component.
    text = re.sub(r"\b(?:[A-Z][A-Za-z0-9_']*\.)+([A-Za-z_][A-Za-z0-9_']*)", r"\1", text)
    return re.sub(r"\s+", "", text)


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    statuses = {}
    for path in (repo / "problems").glob("*/status.json"):
        statuses[path.parent.name] = json.loads(path.read_text()).get("classification")
    completed = {problem for problem, status in statuses.items() if status in DONE}

    entries = []
    unparsed = []
    table_rows = 0
    for number, line in enumerate((repo / "LEMMA-INDEX.md").read_text().splitlines(), 1):
        if not line.startswith("| `"):
            continue
        table_rows += 1
        match = ROW.match(line)
        if not match:
            unparsed.append({"line": number, "text": line})
            continue
        name, where, signature = match.groups()
        where = where.strip()
        if where.startswith("LIB:") or where not in completed:
            continue
        entries.append({"problem_id": where, "lemma": name, "signature": signature,
                        "normalized": normalize(signature)})

    groups: dict[str, list[dict]] = defaultdict(list)
    for entry in entries:
        groups[entry["normalized"]].append(entry)
    clusters = []
    for normalized, members in groups.items():
        problems = sorted({member["problem_id"] for member in members})
        if len(problems) >= 2:
            clusters.append({"normalized": normalized, "problem_count": len(problems),
                             "problems": problems,
                             "members": sorted(members, key=lambda x: (x["problem_id"], x["lemma"]))})
    clusters.sort(key=lambda x: (-x["problem_count"], -len(x["members"]), x["normalized"]))

    payload = {
        "schema_version": 1,
        "source": "LEMMA-INDEX.md generated proved-lemma inventory",
        "completed_classifications": sorted(DONE),
        "completed_problem_count": len(completed),
        "index_rows": table_rows,
        "eligible_problem_lemma_rows": len(entries),
        "cluster_count": len(clusters),
        "normalization": [
            "alpha-rename explicitly typed binder names in encounter order",
            "replace APM problem-local identifier prefixes with apm_local_",
            "strip capitalized namespace qualification to declaration basename",
            "remove all whitespace",
        ],
        "timing": {"status": "deferred", "reason": "LEMMA-INDEX rows carry neither source line nor introduction commit; reliable timing requires source/history attribution across revisions"},
        "unparsed": unparsed,
        "clusters": clusters,
    }
    json_path = repo / "docs/generated/duplicate-solved-lemmas.json"
    md_path = repo / "docs/generated/duplicate-solved-lemmas.md"
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    out = ["# Duplicate proved lemmas in completed problems", "",
           f"Source coverage: {len(entries)} proved helper-lemma rows from {len(completed)} completed problems; {len(unparsed)} index rows unparsed.",
           f"Cross-problem exact-normalized clusters: {len(clusters)}.", "",
           "This is lexical clustering, not Lean definitional equality. Timing is deferred:",
           "the generated index has no source line or introduction commit, and guessing from", 
           "current-file history would not establish which declaration existed first.", "",
           "## Normalization", "",
           "Explicitly typed binder names are alpha-renamed `v0`, `v1`, ... in encounter order;",
           "APM problem-local identifier prefixes become `apm_local_`; capitalized namespace",
           "qualification is reduced to its basename; whitespace is removed. Operators, constants,",
           "binder order, implicit/explicit delimiters, and proposition structure are retained.", "",
           "## Clusters", ""]
    for index, cluster in enumerate(clusters, 1):
        out += [f"### {index}. {cluster['problem_count']} problems / {len(cluster['members'])} declarations", "",
                f"Normalized: `{cluster['normalized']}`", "",
                "| Problem | Lemma | Original signature |", "|---|---|---|"]
        for member in cluster["members"]:
            sig = member["signature"].replace("|", "\\|")
            out.append(f"| {member['problem_id']} | `{member['lemma']}` | `{sig}` |")
        out.append("")
    out += ["## Unparsed index rows", ""]
    if unparsed:
        out += [f"- Line {row['line']}: `{row['text']}`" for row in unparsed]
    else:
        out.append("None.")
    out.append("")
    md_path.write_text("\n".join(out))
    print(f"wrote {json_path.relative_to(repo)}: {len(clusters)} clusters")
    print(f"wrote {md_path.relative_to(repo)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
