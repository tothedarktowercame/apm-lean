#!/usr/bin/env python3
"""Extract a reproducible dependency map from APM frozen Lean statements.

This is deliberately lexical.  It never treats proof outlines or informal
solutions as evidence about the encoded theorem; prose is scanned separately
only for the comparison column.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path


DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
)
IDENT_RE = re.compile(r"(?<![A-Za-z0-9_'])[A-Za-z_][A-Za-z0-9_'.]*(?![A-Za-z0-9_'])")

KEYWORDS = {
    "abbrev", "and", "as", "by", "class", "def", "do", "else", "end",
    "exists", "false", "forall", "fun", "have", "if", "in", "include",
    "instance", "let", "match", "namespace", "noncomputable", "open", "or",
    "private", "protected", "Prop", "Set", "show", "some", "structure",
    "then", "theorem", "true", "Type", "where", "with",
}

# These are observations, not inferred prerequisites.  They intentionally live
# in a separate field from declaration dependencies.
MACHINERY = {
    "alexander-whitney": r"Alexander[–-]Whitney",
    "cellular-homology": r"cellular (?:chain|homology)|CW (?:complex|structure)",
    "cohomology": r"\bcohomolog(?:y|ical)\b|Cohomolog|\bH\^",
    "covering-space": r"\bcovering (?:space|map)|universal cover|CoveringMap",
    "degree-theory": r"\bdegree (?:of|map)|mapping degree",
    "differential-forms": r"differential form|top[ -]form|de Rham",
    "eilenberg-zilber": r"Eilenberg[–-]Zilber",
    "excision": r"\bexcision\b",
    "fundamental-group": r"fundamental group|FundamentalGroup|\\pi_?1|π₁",
    "intersection-theory": r"intersection number|intersection form|self[ -]intersection",
    "kunneth": r"K[üu]nneth",
    "mayer-vietoris": r"Mayer[–-]Vietoris",
    "orientation": r"\borient(?:ed|able|ation|ation-preserving)\b",
    "singular-homology": r"singular homology|singularHomology|\bhomology group|\bH_[0-9*]",
    "stokes": r"Stokes(?:'|’)? theorem",
    "transversality": r"\btransvers(?:e|ality)\b",
    "van-kampen": r"van Kampen|Seifert[–-]van Kampen",
}

# `closer_progress` was not in the original field list for this audit, but it
# is required to reproduce the independently measured 266/475 and 197/319
# coverage ceiling. Keep its provenance explicit rather than folding it into a
# generic text blob.
LEGACY_OBSTRUCTION_FIELDS = (
    "closer_hop", "boundary", "closer_note", "sorry_details", "closer_progress"
)

SINGULAR_HOMOLOGY_RECONCILIATION = [
    {"problem_id": "t01A04", "adjudication": "not statement-required",
     "reason": "frozen statement names covering maps and FundamentalGroup; homology occurs only in later proof commentary"},
    {"problem_id": "t01J05", "adjudication": "statement-required",
     "reason": "conclusion uses apm_t01J05_eulerCharacteristic, whose definition sums finranks of apm_t01J05_H"},
    {"problem_id": "t02A04", "adjudication": "not statement-required",
     "reason": "frozen statement is the fixed-point property; rational homology occurs in bridge_1, not its object definitions"},
    {"problem_id": "t03J02", "adjudication": "statement-required",
     "reason": "frozen statement directly applies apm_t03J02_H in four conjuncts after two let binders"},
    {"problem_id": "t94J08", "adjudication": "statement-required",
     "reason": "t94J08HasDegree unfolds through t94J08TopHomologyMap to singularHomologyFunctor"},
    {"problem_id": "t95J02", "adjudication": "not statement-required",
     "reason": "frozen statement only asserts retractions; H1 occurs in proof bridge declarations"},
]


def mask_comments_and_strings(text: str) -> str:
    """Replace Lean comments and strings with spaces, preserving offsets."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if string:
            out[i] = "\n" if text[i] == "\n" else " "
            if text[i] == "\\" and i + 1 < len(text):
                out[i + 1] = " "
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                i += 1
        elif depth:
            out[i] = "\n" if text[i] == "\n" else " "
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                j = len(text)
            out[i:j] = " " * (j - i)
            i = j
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    return "".join(out)


def declarations(text: str) -> list[dict]:
    masked = mask_comments_and_strings(text)
    matches = list(DECL_RE.finditer(masked))
    result = []
    for pos, match in enumerate(matches):
        end = matches[pos + 1].start() if pos + 1 < len(matches) else len(masked)
        chunk = masked[match.start():end]
        depth = 0
        assign_at = None
        for i, char in enumerate(chunk):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth = max(0, depth - 1)
            elif depth == 0 and chunk.startswith(":=", i):
                # A dependent theorem type may contain `let X := ...`; that is
                # part of the frozen statement, not the declaration body.
                if re.search(r"\blet\s+\S+\s*$", chunk[:i]):
                    continue
                assign_at = i
                break
            elif (depth == 0 and chunk.startswith("where", i)
                  and (i == 0 or not (chunk[i - 1].isalnum()
                                      or chunk[i - 1] in "_'"))
                  and (i + 5 == len(chunk) or not
                       (chunk[i + 5].isalnum() or chunk[i + 5] in "_'"))):
                assign_at = i
                break
        header_end = match.start() + (assign_at if assign_at is not None else len(chunk))
        header = masked[match.start():header_end]
        body = masked[header_end:end]
        result.append({
            "kind": match.group(1), "name": match.group(2),
            "line": masked.count("\n", 0, match.start(2)) + 1,
            "header": " ".join(header.split()),
            "definition_text": " ".join((header + body).split()),
            "body_has_sorry": bool(re.search(r"\bsorry\b", body)),
        })
    return result


def normalized(value: str) -> str:
    return re.sub(r"[^a-z0-9]", "", value.lower())


def select_roots(problem_id: str, decls: list[dict]) -> tuple[list[dict], str]:
    """Select the encoded statement roots without per-problem exceptions.

    Canonical bundles have one normalized ``apm_<problem-id>`` wrapper. Legacy
    bundles often encode a problem as several independent top-level theorems
    and have no wrapper at all; for those, every ``theorem`` (but no helper
    ``lemma``) is a root. A file with no theorem remains unclassified.
    """
    theoremish = [d for d in decls if d["kind"] in {"theorem", "lemma"}]
    target = "apm" + normalized(problem_id)
    exact = [d for d in theoremish if normalized(d["name"]) == target]
    if len(exact) == 1:
        return exact, "normalized apm_<problem-id> match"
    main = [d for d in theoremish if normalized(d["name"]) in {target + "main", normalized(problem_id)}]
    if len(main) == 1:
        return main, "normalized main-name match"
    theorems = [d for d in decls if d["kind"] == "theorem"]
    if theorems:
        return theorems, "legacy split encoding: all top-level theorems"
    if len(theoremish) == 1:
        return theoremish, "only lemma in file"
    return [], "encoded file has no selectable theorem"


def identifiers(header: str) -> set[str]:
    bound: set[str] = set()
    for match in re.finditer(r"[({]\s*([^:{}()]+?)\s*:", header):
        bound.update(IDENT_RE.findall(match.group(1)))
    for match in re.finditer(r"(?:∀|∃|forall|exists)\s+([^,:()]+?)\s*:", header):
        bound.update(IDENT_RE.findall(match.group(1)))
    return {x.strip(".") for x in IDENT_RE.findall(header)
            if x.strip(".") not in KEYWORDS and x.strip(".") not in bound}


def scan_symbols(paths: list[Path]) -> set[str]:
    symbols: set[str] = set()
    for root in paths:
        if not root.exists():
            continue
        for path in root.rglob("*.lean"):
            try:
                masked = mask_comments_and_strings(path.read_text(errors="replace"))
            except OSError:
                continue
            symbols.update(m.group(2) for m in DECL_RE.finditer(masked))
    return symbols


def machinery_mentions(text: str) -> list[str]:
    return sorted(name for name, pattern in MACHINERY.items()
                  if re.search(pattern, text, re.I))


def technique_evidence(text: str) -> list[dict]:
    evidence = []
    for name, pattern in MACHINERY.items():
        match = re.search(pattern, text, re.I)
        if match:
            line = text.count("\n", 0, match.start()) + 1
            excerpt = text.splitlines()[line - 1].strip()
            evidence.append({"technique": name, "method": "informal-solution lexical marker",
                             "line": line, "excerpt": excerpt})
    return evidence


def analyze_bundle(bundle: Path, mathlib_symbols: set[str], ct_symbols: set[str]) -> dict:
    pid = bundle.name
    main_path = bundle / "lean" / "Main.lean"
    informal_text = ((bundle / "informal-solution.md").read_text(errors="replace")
                     if (bundle / "informal-solution.md").exists() else "")
    status_path = bundle / "status.json"
    try:
        status = json.loads(status_path.read_text())
    except (OSError, json.JSONDecodeError):
        status = {}
    structured = status.get("obstructions") if isinstance(status.get("obstructions"), list) else []
    legacy = []
    for field in LEGACY_OBSTRUCTION_FIELDS:
        if field not in status or status[field] is None:
            continue
        raw = status[field]
        text_value = json.dumps(raw, sort_keys=True) if not isinstance(raw, str) else raw
        legacy.append({"field": field, "areas": machinery_mentions(text_value), "value": raw})
    structured_open_areas = sorted({area for item in structured if not item.get("resolved")
                                    for area in item.get("areas", [])})
    legacy_areas = sorted({area for item in legacy for area in item["areas"]})
    noncomplete = status.get("classification") != "complete"
    base = {
        "problem_id": pid,
        "main_file": str(main_path.relative_to(bundle.parents[1])) if main_path.exists() else None,
        "statement_machinery_mentions": [],
        "informal_solution_machinery_mentions": machinery_mentions(informal_text),
        "technique_requirements": technique_evidence(informal_text),
        "classification": status.get("classification"),
        "obstruction_evidence": {
            "has_record": bool(structured or legacy),
            "structured": structured,
            "legacy_by_field": legacy,
            "structured_unresolved_areas": structured_open_areas,
            "legacy_areas": legacy_areas,
            # Structured records supersede legacy prose for ranking on that
            # bundle. This prevents a newer explicit negative such as
            # t02A06's `areas: []` / NOT blocked on Kunneth from being reversed
            # by a lexical hit in its older boundary text.
            "provisional_blocked_areas": sorted(set(structured_open_areas)
                if structured else (set(legacy_areas) if noncomplete else set())),
            "has_explicit_empty_areas": any(item.get("areas") == [] for item in structured),
        },
    }
    if not main_path.exists():
        return base | {"parse_status": "unparseable", "reason": "missing lean/Main.lean"}

    text = main_path.read_text(errors="replace")
    decls = declarations(text)
    roots, method = select_roots(pid, decls)
    if not roots:
        return base | {
            "parse_status": "unparseable", "reason": method,
            "theorem_candidates": [d["name"] for d in decls if d["kind"] in {"theorem", "lemma"}],
        }

    by_name = {d["name"]: d for d in decls}
    root_names = {root["name"] for root in roots}
    closure, frontier = set(), sorted(root_names)
    while frontier:
        name = frontier.pop()
        if name in closure:
            continue
        closure.add(name)
        decl = by_name[name]
        dependency_text = (decl["definition_text"]
                           if name not in root_names and decl["kind"] in
                           {"def", "abbrev", "structure", "class"}
                           else decl["header"])
        for ref in identifiers(dependency_text):
            leaf = ref.rsplit(".", 1)[-1]
            if leaf in by_name and leaf not in closure:
                frontier.append(leaf)

    refs = set()
    for name in closure:
        decl = by_name[name]
        dependency_text = (decl["definition_text"]
                           if name not in root_names and decl["kind"] in
                           {"def", "abbrev", "structure", "class"}
                           else decl["header"])
        refs |= identifiers(dependency_text)
    local_names = set(by_name)
    local_refs = sorted(r for r in refs if r.rsplit(".", 1)[-1] in local_names)
    external = sorted(r for r in refs if r.rsplit(".", 1)[-1] not in local_names)
    provided_mathlib = sorted(r for r in external if r.rsplit(".", 1)[-1] in mathlib_symbols)
    provided_ct = sorted(r for r in external if r.rsplit(".", 1)[-1] in ct_symbols)
    unresolved = sorted(r for r in external
                        if r.rsplit(".", 1)[-1] not in mathlib_symbols | ct_symbols
                        and ("." in r or r[:1].isupper()))

    def dependency_text(name: str) -> str:
        decl = by_name[name]
        return (decl["definition_text"]
                if name not in root_names and decl["kind"] in
                {"def", "abbrev", "structure", "class"}
                else decl["header"])

    paths = {name: [name] for name in sorted(root_names)}
    queue = sorted(root_names)
    while queue:
        name = queue.pop(0)
        for ref in identifiers(dependency_text(name)):
            leaf = ref.rsplit(".", 1)[-1]
            target = ref if ref in by_name else leaf if leaf in by_name else None
            if target and target not in paths:
                paths[target] = paths[name] + [target]
                queue.append(target)

    requirement_evidence: dict[str, list[dict]] = {}
    indexed = mathlib_symbols | ct_symbols
    for name in sorted(closure):
        for ref in sorted(identifiers(dependency_text(name))):
            leaf = ref.rsplit(".", 1)[-1]
            if ref in by_name or leaf in by_name:
                continue
            if not ("." in ref or ref[:1].isupper()) or leaf not in indexed:
                continue
            provider = ("construction-targets" if leaf in ct_symbols
                        else "mathlib")
            item = {"method": "frozen-statement lexical closure",
                    "provider": provider,
                    "local_definition_chain": paths.get(name, [name]),
                    "root_statement": by_name[paths.get(name, [name])[0]]["header"],
                    "source_declaration": name,
                    "source_expression": dependency_text(name)}
            requirement_evidence.setdefault(f"{name}::{ref}", []).append(item)
    object_requirements = [
        {"requirement": requirement, "backing_declaration": requirement.rsplit("::", 1)[1],
         "evidence": evidence}
        for requirement, evidence in sorted(requirement_evidence.items())
    ]
    statement_text = "\n".join(
        (by_name[name]["definition_text"]
         if name not in root_names and by_name[name]["kind"] in
         {"def", "abbrev", "structure", "class"}
         else by_name[name]["header"])
        for name in closure)
    bridges = [d for d in decls if "bridge" in d["name"].lower()]

    return base | {
        "parse_status": "ok", "selection_method": method,
        "frozen_theorem": roots[0]["name"] if len(roots) == 1 else None,
        "frozen_theorem_line": roots[0]["line"] if len(roots) == 1 else None,
        "frozen_statement": roots[0]["header"] if len(roots) == 1 else None,
        "frozen_theorems": [
            {"name": root["name"], "line": root["line"],
             "statement": root["header"], "closed": not root["body_has_sorry"]}
            for root in roots
        ],
        "frozen_theorem_closed": all(not root["body_has_sorry"] for root in roots),
        "bridge_declarations": [
            {"name": d["name"], "line": d["line"], "closed": not d["body_has_sorry"]}
            for d in bridges
        ],
        "statement_machinery_mentions": machinery_mentions(statement_text),
        "local_statement_dependency_closure": sorted(closure),
        "local_declaration_references": local_refs,
        "provided_by_mathlib": provided_mathlib,
        "provided_by_construction_targets": provided_ct,
        "unresolved_declaration_like_references": unresolved,
        "object_requirements": object_requirements,
    }


def blocked_summary(records: list[dict]) -> dict:
    total = len(records)
    noncomplete = [r for r in records if r.get("classification") != "complete"]
    covered = [r for r in records if r["obstruction_evidence"]["has_record"]]
    covered_noncomplete = [r for r in noncomplete if r["obstruction_evidence"]["has_record"]]
    all_areas = sorted({area for r in records
                        for area in r["obstruction_evidence"]["provisional_blocked_areas"]})
    rows = []
    for area in all_areas:
        structured = {r["problem_id"] for r in noncomplete
                      if area in r["obstruction_evidence"]["structured_unresolved_areas"]}
        legacy = {r["problem_id"] for r in noncomplete
                  if not r["obstruction_evidence"]["structured"]
                  and area in r["obstruction_evidence"]["legacy_areas"]}
        object_consumers = [r for r in noncomplete if area in r["statement_machinery_mentions"]]
        object_covered = [r for r in object_consumers if r["obstruction_evidence"]["has_record"]]
        rows.append({"area": area, "blocked_consumers": sorted(structured | legacy),
                     "blocked_count": len(structured | legacy),
                     "structured_count": len(structured), "legacy_count": len(legacy),
                     "object_consumer_coverage": {"covered": len(object_covered),
                                                  "total": len(object_consumers)}})
    rows.sort(key=lambda row: (-row["blocked_count"], row["area"]))
    return {"corpus_coverage": {"covered": len(covered), "total": total},
            "noncomplete_coverage": {"covered": len(covered_noncomplete),
                                     "total": len(noncomplete)},
            "structured_bundle_count": sum(bool(r["obstruction_evidence"]["structured"])
                                           for r in records),
            "legacy_bundle_count": sum(bool(r["obstruction_evidence"]["legacy_by_field"])
                                       for r in records),
            "explicit_empty_areas_bundle_count": sum(
                r["obstruction_evidence"]["has_explicit_empty_areas"] for r in records),
            "ranking_basis": "unweighted unresolved blocked-consumer count; no cost term",
            "areas": rows}


def render_markdown(records: list[dict], generated: str) -> str:
    ok = [r for r in records if r["parse_status"] == "ok"]
    bad = [r for r in records if r["parse_status"] != "ok"]
    not_encoded = [r for r in bad if r.get("reason") == "missing lean/Main.lean"]
    encoded_bad = [r for r in bad if r.get("reason") != "missing lean/Main.lean"]
    statement_counts = Counter(x for r in records for x in r["statement_machinery_mentions"])
    informal_counts = Counter(x for r in records for x in r["informal_solution_machinery_mentions"])
    lines = [
        "# Frozen-statement dependency map", "", f"Generated: {generated}", "",
        "This phase-one artifact is keyed on each frozen Lean theorem signature. Local",
        "definitions mentioned by that signature are followed transitively through their own",
        "signatures. Informal solutions are scanned independently and never contribute to the",
        "statement dependency fields.", "", "## Coverage", "",
        f"- Bundles: {len(records)}", f"- Parsed frozen statements: {len(ok)}",
        f"- Not encoded (no `lean/Main.lean`): {len(not_encoded)}",
        f"- Encoded but unparseable/unclassified: {len(encoded_bad)}",
        f"- Closed parsed frozen theorems: {sum(r['frozen_theorem_closed'] for r in ok)}", "",
        "## Machinery mentions: frozen Lean signatures versus informal solution", "",
        "| Machinery | Statement bundles | Informal-solution bundles |", "|---|---:|---:|",
    ]
    for key in MACHINERY:
        lines.append(f"| {key} | {statement_counts[key]} | {informal_counts[key]} |")
    lines += ["", "These counts are lexical observations included to expose divergence. They are",
              "not the declaration dependency classification.", "", "## Not encoded", ""]
    if not_encoded:
        lines += [f"- `{r['problem_id']}`: {r['reason']}" for r in not_encoded]
    else:
        lines.append("None.")
    lines += ["", "## Encoded but unparseable or unclassified", ""]
    if encoded_bad:
        lines += [f"- `{r['problem_id']}`: {r['reason']}" for r in encoded_bad]
    else:
        lines.append("None.")
    lines += ["", "## Per-bundle compact view", "",
              "Full signatures and declaration lists are in the adjacent JSON artifact.", "",
              "| Problem | Frozen theorem | Closed | Local closure | Unresolved declaration-like | Statement machinery | Informal machinery |",
              "|---|---|---:|---:|---:|---|---|"]
    for r in records:
        if r["parse_status"] != "ok":
            lines.append(f"| {r['problem_id']} | UNPARSEABLE | — | — | — | {', '.join(r['statement_machinery_mentions'])} | {', '.join(r['informal_solution_machinery_mentions'])} |")
        else:
            roots = ", ".join(f"`{root['name']}`" for root in r["frozen_theorems"])
            lines.append(f"| {r['problem_id']} | {roots} | {'yes' if r['frozen_theorem_closed'] else 'no'} | {len(r['local_statement_dependency_closure'])} | {len(r['unresolved_declaration_like_references'])} | {', '.join(r['statement_machinery_mentions'])} | {', '.join(r['informal_solution_machinery_mentions'])} |")
    lines += ["", "## Method limits", "",
              "The extractor is lexical, not Lean's elaborator. A declaration basename found in",
              "Mathlib or ConstructionTargets is reported as available even when namespace, typeclass,",
              "or type mismatches would prevent its use. Conversely, notation and elaborator-generated",
              "dependencies are invisible. `unresolved_declaration_like_references` is therefore an",
              "audit queue, not proof that infrastructure is absent.", "",
              "## Requirement layers", "",
              "`object_requirements` records exact declarations reached from frozen statements,",
              "including the problem-local definition chain and source expression. Its requirement",
              "name combines the local semantic wrapper with the backing declaration, so distinct",
              "instantiations do not collapse merely because both use `singularHomologyFunctor`.",
              "`technique_requirements` records the first matching informal-solution line and remains",
              "a separate, lower-confidence layer; it is never merged into object requirements.", ""]
    lines += ["## Singular-homology method reconciliation", "",
              "The independent first-`apm_*`/whole-body pass reported 36 consumers; this",
              "statement-rooted pass reports 33 after source adjudication.", "",
              "| Problem | Adjudication | Reason |", "|---|---|---|"]
    for item in SINGULAR_HOMOLOGY_RECONCILIATION:
        lines.append(f"| {item['problem_id']} | {item['adjudication']} | {item['reason']} |")
    summary = blocked_summary(records)
    corpus = summary["corpus_coverage"]
    open_cov = summary["noncomplete_coverage"]
    lines += ["", "## Obstruction coverage and provisional blocked-consumer ranking", "",
              f"Corpus coverage: {corpus['covered']}/{corpus['total']} bundles. Non-complete",
              f"coverage: {open_cov['covered']}/{open_cov['total']} bundles. The ranking is",
              "unweighted by cost and is not a funding recommendation.", "",
              "| Area | Blocked consumers | Structured | Legacy text | Object-consumer coverage | Overall obstruction coverage |",
              "|---|---:|---:|---:|---:|---:|"]
    for row in summary["areas"]:
        obj = row["object_consumer_coverage"]
        lines.append(f"| {row['area']} | {row['blocked_count']}/{open_cov['covered']} obstruction-covered non-complete bundles | {row['structured_count']}/{row['blocked_count']} | {row['legacy_count']}/{row['blocked_count']} | {obj['covered']}/{obj['total']} | {open_cov['covered']}/{open_cov['total']} |")
    lines += ["", f"Bundles with an explicit structured `areas: []`: {summary['explicit_empty_areas_bundle_count']}.",
              "Structured and legacy sources remain separate in JSON; their union is used only for",
              "the explicitly provisional ranking above.", ""]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--json", type=Path, default=Path("docs/generated/frozen-statement-dependencies.json"))
    parser.add_argument("--markdown", type=Path, default=Path("docs/generated/frozen-statement-dependencies.md"))
    args = parser.parse_args()
    repo = args.repo.resolve()
    mathlib = repo / ".lake" / "packages" / "mathlib" / "Mathlib"
    mathlib_symbols = scan_symbols([mathlib])
    ct_symbols = scan_symbols([repo / "ConstructionTargets"])
    records = [analyze_bundle(p, mathlib_symbols, ct_symbols)
               for p in sorted((repo / "problems").iterdir()) if p.is_dir()]
    generated = "2026-08-19 (deterministic corpus snapshot; rerun updates content)"
    payload = {
        "schema_version": 3, "generated": generated,
        "method": "frozen theorem signature plus transitive local signature closure",
        "singular_homology_method_reconciliation": SINGULAR_HOMOLOGY_RECONCILIATION,
        "blocked_consumer_summary": blocked_summary(records),
        "records": records,
    }
    json_path = repo / args.json
    md_path = repo / args.markdown
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    md_path.write_text(render_markdown(records, generated))
    print(f"wrote {json_path.relative_to(repo)} ({len(records)} bundles)")
    print(f"wrote {md_path.relative_to(repo)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
