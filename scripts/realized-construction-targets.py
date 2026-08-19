#!/usr/bin/env python3
"""Measure realised ConstructionTargets cost, consumers, and map validation."""

from __future__ import annotations

import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path


IMPORT_RE = re.compile(
    r"(?m)^\s*import\s+ConstructionTargets(?:\.([A-Za-z0-9_]+))?\s*$"
)
DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
)


def git_history_cost(repo: Path, path: Path) -> dict:
    output = subprocess.run(
        ["git", "log", "--follow", "--format=COMMIT %H", "--numstat", "--",
         str(path.relative_to(repo))],
        cwd=repo, check=True, text=True, capture_output=True,
    ).stdout
    commits: set[str] = set()
    added = deleted = 0
    for line in output.splitlines():
        if line.startswith("COMMIT "):
            commits.add(line.removeprefix("COMMIT "))
        elif re.match(r"^\d+\s+\d+\s+", line):
            add, remove, _ = line.split("\t", 2)
            added += int(add)
            deleted += int(remove)
    source_lines = sum(
        1 for line in path.read_text().splitlines()
        if line.strip() and not line.lstrip().startswith("--")
    )
    return {
        "changed_source_lines": added + deleted,
        "lines_added": added,
        "lines_deleted": deleted,
        "touching_commits": len(commits),
        "current_nonblank_noncomment_lines": source_lines,
    }


def imports(path: Path) -> set[str]:
    return {name for name in IMPORT_RE.findall(path.read_text()) if name}


def transitive_modules(seeds: set[str], dependencies: dict[str, set[str]]) -> set[str]:
    result: set[str] = set()
    pending = list(seeds)
    while pending:
        module = pending.pop()
        if module not in result:
            result.add(module)
            pending.extend(dependencies.get(module, set()))
    return result


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    module_paths = {path.stem: path for path in sorted((repo / "ConstructionTargets").glob("*.lean"))}
    dependencies = {name: imports(path) for name, path in module_paths.items()}

    problem_modules: dict[str, set[str]] = {}
    direct_problem_modules: dict[str, set[str]] = {}
    for path in sorted((repo / "problems").glob("*/lean/Main.lean")):
        direct = imports(path)
        # A bare root import exposes every module imported by ConstructionTargets.lean.
        if re.search(r"(?m)^\s*import\s+ConstructionTargets\s*$", path.read_text()):
            direct |= imports(repo / "ConstructionTargets.lean")
        if direct:
            problem_id = path.parents[1].name
            direct_problem_modules[problem_id] = direct
            problem_modules[problem_id] = transitive_modules(direct, dependencies)

    consumers = {
        module: sorted(problem for problem, reached in problem_modules.items()
                       if module in reached)
        for module in module_paths
    }

    statement_map = json.loads(
        (repo / "docs/generated/frozen-statement-dependencies.json").read_text()
    )
    records = {record["problem_id"]: record for record in statement_map["records"]}
    declaration_owners: dict[str, set[str]] = defaultdict(set)
    for module, path in module_paths.items():
        for declaration in DECL_RE.findall(path.read_text()):
            declaration_owners[declaration].add(module)
            declaration_owners[declaration.rsplit(".", 1)[-1]].add(module)

    predictions: dict[str, set[str]] = {}
    for problem in problem_modules:
        predicted: set[str] = set()
        for declaration in records[problem]["provided_by_construction_targets"]:
            predicted |= declaration_owners.get(declaration, set())
        predictions[problem] = predicted

    actual_edges = {(problem, module) for problem, modules in problem_modules.items()
                    for module in modules}
    predicted_edges = {(problem, module) for problem, modules in predictions.items()
                       for module in modules}
    true_positive = actual_edges & predicted_edges
    false_positive = predicted_edges - actual_edges
    false_negative = actual_edges - predicted_edges

    modules = []
    for name, path in module_paths.items():
        cost = git_history_cost(repo, path)
        count = len(consumers[name])
        modules.append({
            "module": name,
            "imports": sorted(dependencies[name]),
            "consumers": consumers[name],
            "consumer_count": count,
            "cost": cost,
            "consumers_per_100_changed_source_lines": (
                100 * count / cost["changed_source_lines"]
                if cost["changed_source_lines"] else None
            ),
            "consumers_per_touching_commit": (
                count / cost["touching_commits"] if cost["touching_commits"] else None
            ),
        })
    modules.sort(key=lambda row: row["module"])

    validation = {
        "population_problem_count": len(problem_modules),
        "actual_transitive_edges": len(actual_edges),
        "predicted_edges": len(predicted_edges),
        "true_positive_edges": len(true_positive),
        "false_positive_edges": len(false_positive),
        "false_negative_edges": len(false_negative),
        "precision": len(true_positive) / len(predicted_edges) if predicted_edges else None,
        "recall": len(true_positive) / len(actual_edges) if actual_edges else None,
        "problems_with_any_correct_prediction": sum(
            bool(problem_modules[p] & predictions[p]) for p in problem_modules
        ),
        "true_positives": sorted([list(edge) for edge in true_positive]),
        "false_positives": sorted([list(edge) for edge in false_positive]),
        "false_negatives": sorted([list(edge) for edge in false_negative]),
        "per_problem": [
            {"problem_id": problem,
             "direct_imports": sorted(direct_problem_modules[problem]),
             "actual_transitive_modules": sorted(problem_modules[problem]),
             "predicted_modules": sorted(predictions[problem])}
            for problem in sorted(problem_modules)
        ],
    }
    payload = {
        "schema_version": 1,
        "cost_unit": "changed source lines: additions plus deletions from git log --follow --numstat",
        "cost_caveat": "line churn weights formatting and rewrites as work, misses thinking and review, and can count shared commits in several modules",
        "consumer_unit": "distinct problem bundles reaching the module through direct or transitive ConstructionTargets imports",
        "modules": modules,
        "validation": validation,
    }
    json_path = repo / "docs/generated/realized-construction-targets.json"
    md_path = repo / "docs/generated/realized-construction-targets.md"
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    lines = [
        "# Realised ConstructionTargets return", "",
        "This is an empirical layer over repository history and imports, not a prediction",
        "of future cost. The primary cost unit is **changed source lines**: additions plus",
        "deletions reported by `git log --follow --numstat` for each module. It is reproducible",
        "and distinguishes differently sized commits, but it counts formatting and rewrites,",
        "misses design/review effort, and charges a shared commit to every module it touches.",
        "Touching commits and current source lines are retained as secondary measurements.", "",
        "Consumers are distinct problem bundles reaching a module through direct or transitive",
        "`ConstructionTargets` imports. They show use, not causal necessity or successful closure.", "",
        "| Module | Changed lines | Touch commits | Current lines | Consumers | Consumers / 100 changed lines |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for row in sorted(modules, key=lambda x: (-x["consumers_per_100_changed_source_lines"], x["module"])):
        cost = row["cost"]
        lines.append(
            f"| {row['module']} | {cost['changed_source_lines']} | {cost['touching_commits']} | "
            f"{cost['current_nonblank_noncomment_lines']} | {row['consumer_count']} | "
            f"{row['consumers_per_100_changed_source_lines']:.3f} |"
        )
    lines += ["", "## Consumers", ""]
    for row in sorted(modules, key=lambda x: (-x["consumer_count"], x["module"])):
        names = ", ".join(f"`{p}`" for p in row["consumers"]) or "none observed"
        lines.append(f"- **{row['module']}** — {row['consumer_count']}/27: {names}")
    lines += [
        "", "`LusinN` has one transitive consumer: `a95J06` imports `BanachZarecki`,",
        "which imports `LusinN`. It is not directly imported and is not unused.", "",
        "## Validation against observed imports", "",
        f"Population: {validation['population_problem_count']} problem bundles with a",
        "ConstructionTargets import. The observed ground truth contains",
        f"{validation['actual_transitive_edges']} transitive problem-module edges.", "",
        f"- Precision: {validation['true_positive_edges']}/{validation['predicted_edges']} = "
        f"{100 * validation['precision']:.1f}%.",
        f"- Recall: {validation['true_positive_edges']}/{validation['actual_transitive_edges']} = "
        f"{100 * validation['recall']:.1f}%.",
        f"- Problems with any correct module prediction: "
        f"{validation['problems_with_any_correct_prediction']}/{validation['population_problem_count']}.",
        f"- False positives: {validation['false_positive_edges']}; false negatives: "
        f"{validation['false_negative_edges']}.", "",
        "A prediction is made only when the frozen-statement map's",
        "`provided_by_construction_targets` declaration resolves to a declaration owned by",
        "a module. The low recall is the result: statement vocabulary usually does not name",
        "the proof infrastructure later imported to close it. The score validates the map as",
        "a topic/object map, not as a reliable predictor of required ConstructionTargets modules.",
        "The two false positives also expose basename collisions in the lexical symbol map.", "",
        "## Reproduce", "", "```sh", "python3 scripts/realized-construction-targets.py", "```", "",
        "The adjacent JSON contains every cost component, import edge, prediction, true",
        "positive, false positive, and false negative.", "",
    ]
    md_path.write_text("\n".join(lines))
    print(f"wrote {json_path.relative_to(repo)}")
    print(f"wrote {md_path.relative_to(repo)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
