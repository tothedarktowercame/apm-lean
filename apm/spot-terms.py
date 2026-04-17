#!/usr/bin/env python3
"""NER term spotter for APM prelim problems.

Loads the futon6 NER kernel, expands APM-specific LaTeX macros,
and spots mathematical terms in problem statements.

Usage:
    python3 spot-terms.py t01A01.tex          # single file
    python3 spot-terms.py --canary            # four canary problems
    python3 spot-terms.py --all               # all 489 problems
    python3 spot-terms.py --check-planetmath  # also check PlanetMath entries
"""

import sys
import os
import re
import json
from pathlib import Path

# --- Paths ---
SCRIPT_DIR = Path(__file__).parent
FUTON6_DIR = Path.home() / "code" / "futon6"
NER_KERNEL = FUTON6_DIR / "data" / "ner-kernel" / "terms.tsv"
PLANETMATH_DIR = Path.home() / "code" / "planetmath"
CANARY_DIR = SCRIPT_DIR.parent / "canary"

CANARY_IDS = ["t01A01", "a96A03", "b03J02", "m96A04"]

# --- APM LaTeX macro expansion ---
# These are fixed abbreviations used across the APM archive.
# Expand them to natural-language equivalents before NER spotting.

MACRO_TABLE = {
    r"\R": "real numbers",
    r"\Rn": "R^n",
    r"\Rtw": "R^2",
    r"\RP": "real projective space",
    r"\C": "complex numbers",
    r"\Z": "integers",
    r"\Son": "S^1",
    r"\Stw": "S^2",
    r"\Sth": "S^3",
    r"\Ttw": "T^2",
    r"\pipe": "|",
    r"\ie": "i.e.",
}


def expand_macros(text):
    """Expand APM-specific LaTeX macros to NER-friendly text."""
    result = text
    # Sort by length descending so \Rtw matches before \R
    for macro, expansion in sorted(MACRO_TABLE.items(), key=lambda x: -len(x[0])):
        result = result.replace(macro, expansion)
    return result


# --- NER kernel loading (adapted from superpod-job.py Stage 5) ---

def load_ner_kernel(path):
    """Load terms.tsv into singles dict and multi-word index."""
    singles = {}   # term_lower -> (term_orig, canon_id)
    multis = {}    # first_content_word -> [(term_lower, term_orig, canon_id)]

    with open(path) as f:
        header = f.readline()  # skip header
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 4:
                continue
            term_lower, term_orig, source, canon = parts[0], parts[1], parts[2], parts[3]

            words = term_lower.split()
            if len(words) == 1:
                singles[term_lower] = (term_orig, canon)
            else:
                # Index by first "content word" (len >= 3)
                first_key = None
                for w in words:
                    if len(w) >= 3:
                        first_key = w
                        break
                if first_key is None:
                    first_key = words[0]
                if first_key not in multis:
                    multis[first_key] = []
                multis[first_key].append((term_lower, term_orig, canon))

    return singles, multis


def spot_terms(text, singles, multis):
    """Spot NER terms in text. Returns list of {term, term_lower, canon}."""
    text_lower = text.lower()

    # Extract words (strip punctuation)
    words = set(re.findall(r"[a-z][a-z'-]*[a-z]|[a-z]", text_lower))

    found = {}

    # Single-word matches
    for w in words:
        if w in singles:
            term_orig, canon = singles[w]
            found[w] = {"term": term_orig, "term_lower": w, "canon": canon}

    # Multi-word matches
    for w in words:
        if w in multis:
            for term_lower, term_orig, canon in multis[w]:
                if term_lower in text_lower and term_lower not in found:
                    found[term_lower] = {
                        "term": term_orig,
                        "term_lower": term_lower,
                        "canon": canon,
                    }

    return sorted(found.values(), key=lambda x: x["term_lower"])


# --- PlanetMath entry checking ---

def load_planetmath_defines():
    """Build a set of all terms defined in PlanetMath (from .edn files).
    Returns canon_id -> {title, file} for quick lookup.

    EDN format uses namespaced maps: #:entry{:id "Foo", :title "foo", ...}
    Each entry is a large map spanning many lines. We extract :id fields
    independently since they are unique per entry and serve as the canon_id
    used by the NER kernel.
    """
    entries = {}
    for edn_file in PLANETMATH_DIR.glob("*.edn"):
        content = edn_file.read_text(errors="replace")
        ids = re.findall(r':id\s+"([^"]+)"', content)
        titles = re.findall(r':title\s+"([^"]*)"', content)
        # IDs and titles appear in same order within the vector of entries
        for entry_id, title in zip(ids, titles):
            entries[entry_id] = {"title": title, "file": edn_file.name}
    return entries


def check_planetmath_coverage(spotted_terms, pm_entries):
    """Check which spotted terms have PlanetMath entries."""
    results = []
    for t in spotted_terms:
        canon = t["canon"]
        has_entry = canon in pm_entries
        entry_info = pm_entries.get(canon, {})
        results.append({
            **t,
            "has_planetmath_entry": has_entry,
            "planetmath_title": entry_info.get("title", ""),
            "planetmath_file": entry_info.get("file", ""),
        })
    return results


# --- Main ---

def process_problem(filepath, singles, multis, pm_entries=None):
    """Process a single .tex file and return coverage report."""
    problem_id = filepath.stem
    raw_text = filepath.read_text()

    # Expand macros
    expanded = expand_macros(raw_text)

    # Spot terms
    terms = spot_terms(expanded, singles, multis)

    # Check PlanetMath if available
    if pm_entries:
        terms = check_planetmath_coverage(terms, pm_entries)

    report = {
        "id": problem_id,
        "filename": filepath.name,
        "terms_spotted": len(terms),
        "terms": terms,
    }

    if pm_entries:
        with_entry = [t for t in terms if t.get("has_planetmath_entry")]
        without_entry = [t for t in terms if not t.get("has_planetmath_entry")]
        report["with_planetmath_entry"] = len(with_entry)
        report["without_planetmath_entry"] = len(without_entry)
        report["coverage_pct"] = (
            round(100 * len(with_entry) / len(terms)) if terms else 0
        )
        report["missing_entries"] = [
            {"term": t["term"], "canon": t["canon"]} for t in without_entry
        ]

    return report


def main():
    args = sys.argv[1:]
    check_pm = "--check-planetmath" in args
    args = [a for a in args if a != "--check-planetmath"]

    # Determine which files to process
    if "--canary" in args:
        files = [SCRIPT_DIR / f"{cid}.tex" for cid in CANARY_IDS]
    elif "--all" in args:
        files = sorted(SCRIPT_DIR.glob("*.tex"))
    elif args:
        files = [SCRIPT_DIR / a if not a.startswith("/") else Path(a) for a in args]
    else:
        print(__doc__)
        sys.exit(1)

    # Load NER kernel
    print(f"Loading NER kernel from {NER_KERNEL}...")
    singles, multis = load_ner_kernel(NER_KERNEL)
    total_terms = len(singles) + sum(len(v) for v in multis.values())
    print(f"  {len(singles)} single-word + {total_terms - len(singles)} multi-word = {total_terms} terms")

    # Load PlanetMath if requested
    pm_entries = None
    if check_pm:
        print(f"Loading PlanetMath entries from {PLANETMATH_DIR}...")
        pm_entries = load_planetmath_defines()
        print(f"  {len(pm_entries)} entries loaded")

    # Process files
    print()
    all_reports = []
    for f in files:
        if not f.exists():
            print(f"  SKIP {f.name}: file not found")
            continue

        report = process_problem(f, singles, multis, pm_entries)
        all_reports.append(report)

        # Print summary
        pm_info = ""
        if check_pm:
            pm_info = (
                f"  PM: {report['with_planetmath_entry']}/{report['terms_spotted']}"
                f" ({report['coverage_pct']}%)"
            )
            if report["missing_entries"]:
                missing_names = [m["term"] for m in report["missing_entries"]]
                pm_info += f"  missing: {', '.join(missing_names[:5])}"
        print(f"  {report['id']}: {report['terms_spotted']} terms spotted{pm_info}")

        # Write per-problem report to canary dir
        report_path = CANARY_DIR / f"{report['id']}-planetmath.edn"
        # Write as simple EDN-compatible format
        with open(report_path, "w") as out:
            out.write(f";; PlanetMath coverage report for {report['id']}\n")
            out.write(f";; Generated by spot-terms.py\n")
            out.write("{\n")
            out.write(f' :id "{report["id"]}"\n')
            out.write(f" :terms-spotted {report['terms_spotted']}\n")
            if check_pm:
                out.write(f" :with-planetmath-entry {report['with_planetmath_entry']}\n")
                out.write(f" :without-planetmath-entry {report['without_planetmath_entry']}\n")
                out.write(f" :coverage-pct {report['coverage_pct']}\n")
            out.write(" :terms [\n")
            for t in report["terms"]:
                canon_str = t["canon"].replace('"', '\\"')
                term_str = t["term"].replace('"', '\\"')
                pm_flag = ""
                if check_pm:
                    pm_flag = f' :has-pm-entry {"true" if t.get("has_planetmath_entry") else "false"}'
                out.write(f'   {{:term "{term_str}" :canon "{canon_str}"{pm_flag}}}\n')
            out.write(" ]\n")
            if check_pm and report.get("missing_entries"):
                out.write(" :missing [\n")
                for m in report["missing_entries"]:
                    out.write(f'   {{:term "{m["term"]}" :canon "{m["canon"]}"}}\n')
                out.write(" ]\n")
            out.write("}\n")

    # Summary
    if len(all_reports) > 1:
        total_spotted = sum(r["terms_spotted"] for r in all_reports)
        print(f"\n  Total: {total_spotted} terms across {len(all_reports)} problems")
        if check_pm:
            total_with = sum(r.get("with_planetmath_entry", 0) for r in all_reports)
            pct = round(100 * total_with / total_spotted) if total_spotted else 0
            print(f"  PlanetMath coverage: {total_with}/{total_spotted} ({pct}%)")

    print(f"\nReports written to {CANARY_DIR}/")


if __name__ == "__main__":
    main()
