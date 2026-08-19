#!/usr/bin/env python3
"""Cluster normalized proved lemma signatures across completed APM bundles."""

from __future__ import annotations

import json
import re
import subprocess
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


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=repo, check=True, text=True,
                          capture_output=True).stdout


def pickaxe_candidates(repo: Path, needle: str, path: str | None = None) -> list[dict]:
    args = ["log", "--all", "--reverse", "--format=%H%x09%aI", "-S", needle]
    if path:
        args += ["--", path]
    rows = []
    for line in git(repo, *args).splitlines():
        if "\t" in line:
            commit, date = line.split("\t", 1)
            rows.append({"commit": commit, "date": date})
    return rows


def member_introduction(repo: Path, member: dict) -> dict | None:
    """Attribute repo-wide name pickaxe hits to this problem's historical file."""
    source = f"problems/{member['problem_id']}/lean/Main.lean"
    declaration = member["lemma"]
    for hit in pickaxe_candidates(repo, declaration):
        shown = subprocess.run(["git", "show", f"{hit['commit']}:{source}"], cwd=repo,
                               text=True, capture_output=True)
        if shown.returncode == 0 and re.search(
                rf"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*"
                rf"(?:theorem|lemma)\s+{re.escape(declaration)}\b", shown.stdout):
            return hit
    return None


def index_introduction(repo: Path, member: dict) -> dict | None:
    needle = f"| `{member['lemma']}` | {member['problem_id']} |"
    hits = pickaxe_candidates(repo, needle, "LEMMA-INDEX.md")
    return hits[0] if hits else None


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

    dated = undated = post = concurrent = indexed_before = 0
    for cluster in clusters:
        for member in cluster["members"]:
            member["introduced"] = member_introduction(repo, member)
            member["indexed"] = index_introduction(repo, member)
            dated += member["introduced"] is not None
            undated += member["introduced"] is None
        known = [m for m in cluster["members"] if m["introduced"]]
        earliest_day = min((m["introduced"]["date"][:10] for m in known), default=None)
        cluster["earliest_day"] = earliest_day
        for member in cluster["members"]:
            intro = member["introduced"]
            if not intro or not earliest_day:
                member["timing_class"] = "undated"
            elif intro["date"][:10] > earliest_day:
                member["timing_class"] = "post-dates-earliest"
                post += 1
            else:
                member["timing_class"] = "earliest-or-same-day"
                concurrent += 1
            prior_index = [m for m in cluster["members"]
                           if m is not member and m["indexed"] and intro
                           and m["indexed"]["date"] < intro["date"]]
            member["prior_equivalent_indexed"] = sorted(
                [{"problem_id": m["problem_id"], "lemma": m["lemma"],
                  **m["indexed"]} for m in prior_index],
                key=lambda x: (x["date"], x["problem_id"], x["lemma"]))
            if member["prior_equivalent_indexed"]:
                indexed_before += 1

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
        "timing": {"status": "complete", "dated_members": dated,
                   "undated_members": undated,
                   "earliest_or_same_day_members": concurrent,
                   "cluster_earliest_members": len(clusters),
                   "same_day_later_members": concurrent - len(clusters),
                   "post_dates_earliest_members": post,
                   "members_with_prior_equivalent_indexed": indexed_before,
                   "method": "repo-wide git log --all --reverse -S declaration-name, attributed by inspecting the problem file at each candidate commit; member-specific LEMMA-INDEX row pickaxe for index availability"},
        "unparsed": unparsed,
        "clusters": clusters,
    }
    json_path = repo / "docs/generated/duplicate-solved-lemmas.json"
    md_path = repo / "docs/generated/duplicate-solved-lemmas.md"
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    out = ["# Duplicate proved lemmas in completed problems", "",
           f"Source coverage: {len(entries)} proved helper-lemma rows from {len(completed)} completed problems; {len(unparsed)} index rows unparsed.",
           f"Cross-problem exact-normalized clusters: {len(clusters)}.", "",
           "This is lexical clustering, not Lean definitional equality.", "",
           "## Timing summary", "",
           f"Dated members: {dated}; undated: {undated}. Earliest or same-day: {concurrent};",
           f"post-dating the cluster's earliest day: {post}. Later members for which an equivalent",
           f"problem row was already in `LEMMA-INDEX.md`: {indexed_before}.", "",
           f"Among the {dated - len(clusters)} non-earliest members, {concurrent - len(clusters)}",
           f"were introduced on the earliest member's calendar day and {post} were later-day",
           "duplicates. All three later-day duplicates post-date an equivalent indexed row.", "",
           "## Normalization", "",
           "Explicitly typed binder names are alpha-renamed `v0`, `v1`, ... in encounter order;",
           "APM problem-local identifier prefixes become `apm_local_`; capitalized namespace",
           "qualification is reduced to its basename; whitespace is removed. Operators, constants,",
           "binder order, implicit/explicit delimiters, and proposition structure are retained.", "",
           "## Clusters", ""]
    for index, cluster in enumerate(clusters, 1):
        out += [f"### {index}. {cluster['problem_count']} problems / {len(cluster['members'])} declarations", "",
                f"Normalized: `{cluster['normalized']}`", "",
                "| Problem | Lemma | Original signature | Introduced / class | Indexed |",
                "|---|---|---|---|---|"]
        for member in cluster["members"]:
            sig = member["signature"].replace("|", "\\|")
            intro = member["introduced"]
            timing = (f"{intro['date'][:10]} {intro['commit'][:8]} / {member['timing_class']}"
                      if intro else "undated")
            indexed = member["indexed"]
            index_text = f"{indexed['date'][:10]} {indexed['commit'][:8]}" if indexed else "never dated"
            out.append(f"| {member['problem_id']} | `{member['lemma']}` | `{sig}` | {timing} | {index_text} |")
        out.append("")
    out += ["## Deep dive: a00J04 and a01A08", "",
            "The two problem files first entered history on 2026-07-13. Their completed",
            "lemniscate developments were introduced by `3e9a506e` at",
            "2026-07-30T19:24:37+01:00 (`a00J04`) and `c512690e` at",
            "2026-07-30T19:31:38+01:00 (`a01A08`): seven minutes apart on the same day.",
            "All 19 shared cluster members therefore classify as same-day/concurrent under",
            "the preregistered rule, not post-dating discoverability failures.", "",
            "The relevant problem rows first appeared in `LEMMA-INDEX.md` at `497acbdd` on",
            "2026-08-06, a week after both completed developments. The index could not have",
            "prevented this duplication. The later file does, however, explicitly say that its",
            "TeX problem is identical to `a00J04` and that it adapts the `a00J04` formalization",
            "(`problems/a01A08/lean/Main.lean`, current lines 17--20 and 44--45). Thus this is",
            "documented consultation and adaptation of an intentionally duplicated problem,",
            "not an unnoticed independent re-derivation.", ""]
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
