#!/usr/bin/env python3
"""Transitive dependency extraction for APM frozen statements.

WHY THIS EXISTS. Two weaker passes preceded it and both misled:

  1. Marker survey over problem.md + informal-solution.md
     (scripts/survey-machinery-markers.py). Measures what the PAPER PROOF uses.
     Reported 58 problems needing topology machinery, 52 open, 5 needing
     Kunneth. Retracted: only 16 of the 58 mention machinery in a STATEMENT, and
     ZERO of the 5 Kunneth problems do.

  2. Mentions-only extraction from the frozen theorem text. Measures what the
     STATEMENT names directly. Reported t02A06 as referencing only `Fin` --
     i.e. needing no infrastructure at all. Also wrong, and worse: t02A06's
     third conjunct calls `apm_t02a06_H3Map`, defined twelve lines above the
     theorem as `AlgebraicTopology.singularHomologyFunctor ...`. The dependency
     is one hop through a problem-local def, and a mentions-only pass cannot
     see it.

THE CORRECTED FINDING, from claude-10: t02A06 DEPENDS on singular homology and
does NOT depend on Kunneth. The overclaim was Kunneth specifically, not
machinery in general. Both errors point the same way -- a pass that cannot
follow problem-local definitions will systematically misreport, in EITHER
direction.

WHAT THIS DOES. Starts at the frozen `apm_*` theorem, collects referenced
identifiers, and follows every problem-local definition (`apm_*`, `T<digits>*`)
TRANSITIVELY, accumulating the non-local declarations reached. That is the
minimum bar for an honest dependency map.

WHAT IT STILL IS NOT. Source-level closure, not elaboration. It cannot see
declarations introduced by instance resolution, unfolding, or notation. The
honest next rung is a Lean metaprogram collecting the constant set from the
elaborated environment. Until then, treat a disagreement with the elaborator as
the elaborator winning.

ACCEPTANCE TEST (claude-10, 2026-08-19), and it cuts both ways:
    t02A06 must be reported as depending on singular homology
    t02A06 must NOT be reported as depending on Kunneth
"""
import argparse, json, os, re, sys, collections

LOCAL = re.compile(r'^(apm_|T\d|t\d)', re.I)
IDENT = re.compile(r'\b([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_\']*)*)\b')

# what each Mathlib area means for the dependency map
AREAS = {
    'singular-homology': r'singularHomology|AlgebraicTopology|ChainComplex|HomologicalComplex',
    'kunneth':           r'[Kk]unneth|[Kk]ünneth|tensorProduct.*homology',
    'covering-space':    r'IsCoveringMap|SimplyConnected|Covering',
    'manifold':          r'IsManifold|ChartedSpace|ModelWithCorners|ContMDiff|Boundaryless',
    'measure-integral':  r'MeasureTheory|Integrable|volume|eLpNorm|MemLp',
    'intersection':      r'crossProduct|dotProduct|Transversal|intersectionNumber',
    'metric-topology':   r'Metric\.|EuclideanSpace|Homeomorph|Topology\.',
}


def defs_in(src):
    """Map problem-local declaration name -> its source body."""
    out = {}
    pat = re.compile(r'^(?:noncomputable\s+)?(?:private\s+)?(?:def|abbrev|structure|theorem|lemma)\s+([A-Za-z_][\w\']*)',
                     re.M)
    hits = list(pat.finditer(src))
    for i, m in enumerate(hits):
        end = hits[i + 1].start() if i + 1 < len(hits) else len(src)
        out[m.group(1)] = src[m.start():end]
    return out


def closure(src, root):
    """Transitively follow problem-local defs from ROOT; return non-local decls."""
    bodies = defs_in(src)
    seen, queue, external = set(), [root], collections.Counter()
    while queue:
        name = queue.pop()
        if name in seen:
            continue
        seen.add(name)
        body = bodies.get(name)
        if body is None:
            continue
        for ident in IDENT.findall(body):
            if ident == name:
                continue
            if LOCAL.match(ident):
                if ident in bodies and ident not in seen:
                    queue.append(ident)
            elif ident[0].isupper() or '.' in ident:
                external[ident] += 1
    return seen, external


def areas_for(external):
    joined = ' '.join(external)
    return sorted(a for a, pat in AREAS.items() if re.search(pat, joined))


def analyse(pid):
    path = f'problems/{pid}/lean/Main.lean'
    if not os.path.exists(path):
        return {'problem': pid, 'error': 'no Main.lean'}
    src = open(path, errors='replace').read()
    # Two naming conventions in this corpus. Most bundles freeze an `apm_*`
    # theorem; 92 of 448 use domain names (a00J01 `eLpNorm_tendsto_top`,
    # a01A02 `weakL2_implies_L1_bound`) and carry zero sorries -- an older,
    # already-complete shape. Requiring `apm_` silently dropped all 92 and
    # reported 356/448 as if it were the corpus. Fall back to the LAST
    # top-level theorem, which is where the frozen statement conventionally
    # sits, and RECORD which convention was used so the two populations stay
    # distinguishable rather than being silently merged.
    m = re.search(r'^theorem\s+(apm_\w+)', src, re.M)
    if m:
        root, convention = m.group(1), 'apm-named'
    else:
        alts = re.findall(r'^(?:noncomputable\s+)?theorem\s+([A-Za-z_][\w\']*)', src, re.M)
        if not alts:
            return {'problem': pid, 'error': 'no top-level theorem'}
        root, convention = alts[-1], 'last-theorem-fallback'
    followed, external = closure(src, root)
    try:
        cls = json.load(open(f'problems/{pid}/status.json')).get('classification')
    except Exception:
        cls = '?'
    return {'problem': pid, 'classification': cls, 'root': root,
            'root_convention': convention,
            'local_defs_followed': sorted(followed - {root}),
            'areas': areas_for(external),
            'top_external': [d for d, _ in external.most_common(12)]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('problems', nargs='*', help='problem ids (default: all with a Main.lean)')
    ap.add_argument('--json', action='store_true')
    ap.add_argument('--self-test', action='store_true', help='run the t02A06 acceptance test')
    args = ap.parse_args()

    if args.self_test:
        r = analyse('t02A06')
        ok_h = 'singular-homology' in r.get('areas', [])
        ok_k = 'kunneth' not in r.get('areas', [])
        print(f"  t02A06 areas: {r.get('areas')}")
        print(f"  followed {len(r.get('local_defs_followed', []))} local defs")
        print(f"  [{'PASS' if ok_h else 'FAIL'}] depends on singular homology")
        print(f"  [{'PASS' if ok_k else 'FAIL'}] does NOT depend on Kunneth")
        sys.exit(0 if (ok_h and ok_k) else 1)

    # NB: dirname of problems/<pid>/lean/Main.lean is .../lean, so the problem
    # id is TWO levels up. Getting this wrong yields 448 rows of "no Main.lean"
    # that look like a completed survey -- caught 2026-08-19.
    pids = args.problems or sorted(
        os.path.basename(os.path.dirname(os.path.dirname(p)))
        for p in __import__('glob').glob('problems/*/lean/Main.lean'))
    rows = [analyse(p) for p in pids]
    if args.json:
        print(json.dumps(rows, indent=2))
        return
    for r in rows:
        if 'error' in r:
            print(f"  {r['problem']:9} -- {r['error']}")
            continue
        print(f"  {r['problem']:9} {r['classification']:14} "
              f"defs={len(r['local_defs_followed']):3}  areas={','.join(r['areas']) or '(none)'}")


if __name__ == '__main__':
    main()
