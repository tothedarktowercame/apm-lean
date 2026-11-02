#!/usr/bin/env python3
"""First skill clustering for the prelim star map: group problems by rare shared
Mathlib constants, weighted by inverse document frequency.  Prints each community
with its most characteristic constants.  Writes clusters.json."""
import collections, glob, json, math, os, re, sys
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
SKIP_MOD = re.compile(r'^(Init|Std|Lean|Batteries|Aesop|Qq)|^Mathlib\.(Tactic|Logic|Order\.Basic|Algebra\.Group\.Defs|Algebra\.Ring\.Defs)')
SKIP_NAME = re.compile(r'(^|\.)inst|_simp_|_proof_|\.match_|\.rec$|\.casesOn|\.noConfusion|\.mk$|toFun|\.to[A-Z]|_aux|_eq_1$|Tactic|\.sizeOf')
docs = {}
for f in glob.glob(HERE + '/deps/*.tsv'):
    pid = os.path.basename(f)[:-4]
    s = set()
    for l in open(f):
        p = l.rstrip('\n').split('\t')
        if len(p) != 4 or p[0] != 'DEP':
            continue
        _, name, mod, kind = p
        if kind not in ('thm', 'def', 'ind'):
            continue
        if SKIP_MOD.search(mod) or SKIP_NAME.search(name):
            continue
        s.add(name)
    if s:
        docs[pid] = s
N = len(docs)
df = collections.Counter(c for s in docs.values() for c in s)
idf = {c: math.log(N / df[c]) for c in df}
use = {c for c in df if 2 <= df[c] <= 0.12 * N}
vec = {p: {c: idf[c] for c in s & use} for p, s in docs.items()}
norm = {p: math.sqrt(sum(v * v for v in x.values())) or 1 for p, x in vec.items()}
post = collections.defaultdict(list)
for p, x in vec.items():
    for c in x:
        post[c].append(p)
sim = collections.Counter()
for c, ps in post.items():
    w = idf[c] ** 2
    for i, a in enumerate(ps):
        for b in ps[i + 1:]:
            sim[tuple(sorted((a, b)))] += w
G = nx.Graph()
G.add_nodes_from(docs)
top = collections.defaultdict(list)
for (a, b), s in sim.items():
    v = s / (norm[a] * norm[b])
    top[a].append((v, b)); top[b].append((v, a))
for a, l in top.items():
    for v, b in sorted(l, reverse=True)[:8]:
        if v > 0.05:
            G.add_edge(a, b, weight=v)
comms = nx.community.louvain_communities(G, weight='weight', seed=1, resolution=float(sys.argv[1]) if len(sys.argv) > 1 else 1.5)
comms = sorted(comms, key=len, reverse=True)
res = []
for c in comms:
    cnt = collections.Counter(x for p in c for x in vec[p])
    score = {x: (cnt[x] / len(c)) * math.log(N / df[x]) * (cnt[x] / df[x]) for x in cnt}
    best = sorted(score, key=score.get, reverse=True)[:8]
    sub = collections.Counter(p[0] for p in c)
    res.append({'size': len(c), 'subjects': dict(sub), 'problems': sorted(c), 'keys': best})
json.dump(res, open(HERE + '/clusters.json', 'w'), ensure_ascii=False, indent=1)
print('problems', N, 'used constants', len(use), 'communities', len(res))
for i, r in enumerate(res):
    print(f"\n#{i} n={r['size']} {r['subjects']} e.g. {r['problems'][:5]}")
    print('   ' + ', '.join(r['keys'][:7]))
