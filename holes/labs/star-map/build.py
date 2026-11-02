#!/usr/bin/env python3
"""Star-map skills: a named vocabulary (concepts.tsv) tied to each problem by two independent sources.

  informal  the skill is named in the problem's informal solution or a mark8 warrant
  lean      the Lean proof reaches a Mathlib constant matching the skill's constant regex

Tiers: both = both sources agree; named = no Lean match but the informal side is emphatic (three or
more mentions, or one plus a mark8 warrant or the problem statement); passing = other mentions;
lean = reached only.  A blind sample (sample-*.tsv, README) supports both and named as study tags.  Only theorems and
named definitions count on the Lean side, not typeclass projections or instances, which a proof
reaches without anyone meaning to use the idea.  The "enriched" list shows constants most
over-represented among problems that name the skill.  It is display only: being picked from those
same problems, it cannot count as a second source.  mark8 steps whose warrant names the skill are
attached as readable examples.

Writes star-map.json and STAR-MAP.md.  Stdlib + scipy."""
import collections, glob, json, math, os, re, sys
from scipy.stats import hypergeom
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..', '..')
ALIGN = os.path.expanduser('~/code/storage/apm/mining/alignment')
SKIP_NAME = re.compile(r'(^|\.)inst|_simp_|_proof_|\.match_|\.rec$|\.casesOn|\.noConfusion|_aux|_eq_1$|\.sizeOf')
SKIP_MOD = re.compile(r'^(Init|Std|Lean|Batteries|Aesop|Qq)|^Mathlib\.Tactic')
PROJECTION = re.compile(r'\.to[A-Z]|\.of[A-Z]|\.is[A-Z]\w*$|Space$|\.[a-z]\w*(?:Ring|Monoid|Group|Algebra|Module|Action|Semiring|Lattice|Structure)\b|funLike|Class\b|_inst|(?:^|\.)[a-z]\w*(?:Space|Topology)$')

def concepts():
    out = []
    for l in open(HERE + '/concepts.tsv', encoding='utf8'):
        if l.startswith('#') or not l.strip():
            continue
        p = l.rstrip('\n').split('\t') + ['']
        out.append({'area': p[0], 'skill': p[1], 'text': re.compile(p[2], re.I),
                    'lean': re.compile(p[3]) if p[3] else None})
    return out

def lean_deps():
    docs = {}
    for f in glob.glob(HERE + '/deps/*.tsv'):
        pid = os.path.basename(f)[:-4]
        s = {}
        for l in open(f):
            p = l.rstrip('\n').split('\t')
            if len(p) == 4 and p[0] == 'DEP' and p[3] in ('thm', 'def', 'ind') \
               and not SKIP_MOD.search(p[2]) and not SKIP_NAME.search(p[1]):
                s[p[1]] = p[2]
        if s:
            docs[pid] = s
    return docs

def steps(pid):
    f = f'{ALIGN}/r2-judged/{pid}.judged.json'
    if not os.path.exists(f):
        f = f'{ALIGN}/r2-all/{pid}.alignment.json'
    if not os.path.exists(f):
        return []
    return json.load(open(f)).get('non_hole_steps', [])

def statement(pid):
    f = f'{ROOT}/problems/{pid}/problem.tex'
    return open(f, errors='ignore').read() if os.path.exists(f) else ''

def render(res, pids):
    out = ['# Prelim star map: skills', '',
           f'{len(res)} skills over {len(pids)} problems. `both` means the informal solution names the skill',
           'and the Lean proof reaches a matching Mathlib constant. `named` means the informal side alone',
           'names it emphatically. Tags are for study planning and carry the error rates in README.md.',
           'Built by build.py; edit concepts.tsv, not this file.', '']
    area = None
    for s in res:
        if s['area'] != area:
            area = s['area']
            out += [f'## {area}', '']
        tag = s['both'] + s['named']
        out += [f"### {s['skill']} ({len(s['both'])} both, {len(s['named'])} named)", '']
        if s['both']:
            out.append('both: ' + ' '.join(f'`{p}`' for p in s['both']))
        if s['named']:
            out.append('named: ' + ' '.join(f'`{p}`' for p in s['named']))
        if s['constants']:
            out += ['', 'Lean: ' + ', '.join(f'`{c}`' for c in s['constants'][:5])]
        for e in s['steps'][:2]:
            lean = f" Lean: `{e['lean']}`." if e['lean'] else ''
            out += ['', f"- {e['problem']}: {' '.join(e['step'].split())} (warrant: {' '.join(e['warrant'].split())}).{lean}"]
        out.append('')
    open(HERE + '/STAR-MAP.md', 'w', encoding='utf8').write('\n'.join(out))

def main():
    C = concepts()
    lean = lean_deps()
    pids = sorted(lean)
    N = len(pids)
    df = collections.Counter(c for s in lean.values() for c in s)
    sol = {}
    stm = {}
    st = {}
    for p in pids:
        f = f'{ROOT}/problems/{p}/informal-solution.md'
        t = open(f, errors='ignore').read().replace('’', "'") if os.path.exists(f) else ''
        st[p] = steps(p)
        sol[p] = t
        stm[p] = statement(p).replace('’', "'")
    res = []
    tags = collections.defaultdict(list)
    for c in C:
        named = {}
        for p in pids:
            n = len(c['text'].findall(sol[p]))
            q = len(c['text'].findall(stm[p]))
            w = [s for s in st[p] if c['text'].search(s.get('warrant') or '')]
            if n or q or w:
                named[p] = (n, w, q)
        hand = {x for x in df if c['lean'] and c['lean'].search(x) and df[x] <= 0.25 * N and not PROJECTION.search(x)}
        # Over-represented constants, found without the hand regex.
        enr = []
        if len(named) >= 3:
            cnt = collections.Counter(x for p in named for x in lean[p])
            for x, k in cnt.items():
                if df[x] < 3 or df[x] > 0.15 * N or k < 3 or k / df[x] < 0.5:
                    continue
                pv = hypergeom.sf(k - 1, N, df[x], len(named))
                if pv < 1e-5:
                    enr.append((pv, x, k, df[x]))
            enr.sort()
        enr_c = {x for _, x, _, _ in enr}
        both, inf, weak, le = [], [], [], []
        for p in pids:
            if p in named and hand & lean[p].keys():
                both.append(p)
            elif p in named:
                n, w, q = named[p]
                (inf if n >= 3 or (n >= 1 and (w or q)) else weak).append(p)
            elif hand & lean[p].keys():
                le.append(p)
        ex = []
        for p in sorted(named, key=lambda p: -len(named[p][1])):
            for s in named[p][1]:
                good = s.get('matched') and not re.match(r'(None|Neither|No )', s.get('judge_reason') or '')
                ex.append((0 if good else 1, p, s.get('step', '')[:160], s.get('warrant', '')[:70], s.get('lemma') if good else None))
        ex.sort(key=lambda e: e[0])
        seen, ex2 = set(), []
        for e in ex:
            if e[1] not in seen:
                seen.add(e[1]); ex2.append({'problem': e[1], 'step': e[2], 'warrant': e[3], 'lean': e[4]})
            if len(ex2) == 3:
                break
        top = collections.Counter(x for p in both for x in lean[p] if x in hand)
        mods = collections.Counter(lean[p][x] for p in both for x in lean[p] if x in hand)
        res.append({'area': c['area'], 'skill': c['skill'], 'both': both, 'named': inf, 'passing': weak, 'lean_only': le,
                    'constants': [x for x, _ in top.most_common(6)], 'modules': [m for m, _ in mods.most_common(3)],
                    'enriched': [x for _, x, _, _ in enr[:6]], 'steps': ex2, 'hand_constants': len(hand)})
        for t, ps in (('both', both), ('named', inf), ('passing', weak), ('lean', le)):
            for p in ps:
                tags[p].append((c['skill'], t))
    json.dump({'problems': N, 'skills': res, 'tags': tags}, open(HERE + '/star-map.json', 'w'), ensure_ascii=False, indent=1)
    cov = [sum(1 for p in pids if sum(t in ('both', 'named') for _, t in tags[p]) >= i) for i in (1, 2, 3)]
    print('skills', len(res), 'problems', N, 'with >=1/2/3 study tags', cov, 'tiers', collections.Counter(t for p in pids for _, t in tags[p]))
    print('no study tag', [p for p in pids if not any(t in ('both', 'named') for _, t in tags[p])])
    print('skills with <3 both', [s['skill'] for s in res if len(s['both']) < 3])
    render(res, pids)
    for s in res:
        print(f"{s['area'][:9]:9} {len(s['both']):3d} +{len(s['named']):3d}n +{len(s['passing']):3d}p +{len(s['lean_only']):3d}l  {s['skill']}")
main()
