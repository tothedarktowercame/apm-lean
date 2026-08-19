#!/usr/bin/env python3
"""Survey APM problem bundles for topology-machinery markers.

PROVENANCE AND ITS DEFECT — read before using the numbers.

Written 2026-08-18 by claude-2 (ground control) to answer "do other problems
need the same machinery as t01A05, or is it the only one?". It reported 58
problems in the machinery union, 52 of them open, and 5 naming Kunneth.

That framing was RETRACTED on 2026-08-19 after claude-10 established, from
t02A06, that the encoded second conjunct needs only `H2(S^2) != 0` plus a
retract argument -- NOT Kunneth. The informal solution reaches for Kunneth
because it is the natural paper argument, not the cheapest Lean route.

Re-running with provenance showed the defect is systematic, not a one-off:

    machinery union                                  58
    ... mentioned in the STATEMENT                   16
    ... i.e. informal-solution only                  42
    Kunneth problems mentioned in a STATEMENT         0  (all 5 are informal-only)

So this script measures WHAT THE PAPER PROOF USES, not WHAT THE ENCODING
DEMANDS, and it overstates the machinery requirement by roughly threefold as a
claim about corpus need.

WHAT IT IS STILL GOOD FOR. Kept deliberately as the SECOND COLUMN of a
statement-keyed dependency map: the DIVERGENCE between "what the paper uses"
and "what the encoding needs" is a signal in its own right, and following it is
how t02A06 found a cheaper route. Use --provenance to see which side a hit came
from; a statement/informal disagreement is the interesting row.

DO NOT use this alone to commission machinery. Key that on the frozen Lean
statements, where the elaborator is ground truth.
"""
import argparse, collections, glob, json, os, re

MARKERS = {
    'covering':         r'\bcovering (map|space)\b|\bk-sheeted\b|\bsheeted\b',
    'intersection':     r'intersection number|transversal',
    'form-integration': r'\\int_\{?\\?tilde|\\Omega\^n|differential form|\bStokes\b|top form',
    'homology':         r'\bhomolog|\bcohomolog|\bfundamental class\b',
    'kunneth':          r'K[u\u00fc]nneth',
}
# the union that was reported as "needs t01A05-class machinery"
UNION = ('covering', 'intersection', 'form-integration')


def classification(pid):
    try:
        return json.load(open(f'problems/{pid}/status.json')).get('classification')
    except Exception:
        return '?'


def survey(root='problems'):
    rows = {}
    for f in sorted(glob.glob(f'{root}/*/problem.md')):
        pid = os.path.basename(os.path.dirname(f))
        stmt = open(f, errors='replace').read()
        inf_path = f.replace('problem.md', 'informal-solution.md')
        inf = open(inf_path, errors='replace').read() if os.path.exists(inf_path) else ''
        hit = {}
        for name, pat in MARKERS.items():
            in_stmt = bool(re.search(pat, stmt, re.I))
            in_inf = bool(re.search(pat, inf, re.I))
            if in_stmt or in_inf:
                hit[name] = ('statement' if in_stmt else '') + ('+informal' if in_inf else '')
        if hit:
            rows[pid] = {'markers': hit, 'classification': classification(pid)}
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--provenance', action='store_true',
                    help='show statement vs informal for every hit')
    ap.add_argument('--json', action='store_true', help='emit JSON')
    args = ap.parse_args()

    rows = survey()
    if args.json:
        print(json.dumps(rows, indent=2, sort_keys=True))
        return

    union = {p for p, r in rows.items() if any(m in r['markers'] for m in UNION)}
    stmt_union = {p for p in union
                  if any('statement' in rows[p]['markers'].get(m, '') for m in UNION)}
    openish = {p for p in union if rows[p]['classification'] in ('partial', 'informal-only')}

    print(f'surveyed bundles with any marker : {len(rows)}')
    print(f'machinery union (cover|inter|form): {len(union)}')
    print(f'  ... still open                  : {len(openish)}')
    print(f'  ... mentioned in the STATEMENT  : {len(stmt_union)}   <-- the actionable number')
    print(f'  ... informal-solution only      : {len(union) - len(stmt_union)}')
    kun = {p: r for p, r in rows.items() if 'kunneth' in r['markers']}
    print(f'\nKunneth mentions: {len(kun)}')
    for p, r in sorted(kun.items()):
        print(f'  {p}  [{r["markers"]["kunneth"]:18}]  {r["classification"]}')
    print('  NOTE: zero of these appear in a problem STATEMENT. t02A06 was shown')
    print('        to need only H2 of spheres plus a retract -- no Kunneth.')

    if args.provenance:
        print('\nper-problem provenance:')
        for p in sorted(union):
            ms = ' '.join(f'{k}[{v}]' for k, v in sorted(rows[p]['markers'].items()))
            print(f'  {p}  {rows[p]["classification"]:14} {ms}')


if __name__ == '__main__':
    main()
