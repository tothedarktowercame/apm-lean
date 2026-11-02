#!/usr/bin/env python3
"""Blind sample of (problem, skill) rows for an outside precision check.  Writes sample-rows.tsv for
the reader (no tiers) and sample-key.tsv (tiers).  Controls are untagged skills from the problem's own
area, which measure how many true uses the tagger misses."""
import json, random, sys
d = json.load(open('star-map.json'))
area = {s['skill']: s['area'] for s in d['skills']}
rows = {'both': [], 'informal': [], 'lean': [], 'untagged': []}
tags = d['tags']
for p, ts in tags.items():
    for s, t in ts:
        rows[t].append((p, s))
    tagged = {s for s, _ in ts}
    areas = {area[s] for s in tagged}
    rows['untagged'] += [(p, s) for s in area if area[s] in areas and s not in tagged]
r = random.Random(7)
out = []
for t, n in (('both', 25), ('informal', 25), ('lean', 25), ('untagged', 25)):
    out += [(p, s, t) for p, s in r.sample(sorted(rows[t]), n)]
r.shuffle(out)
print({t: len(v) for t, v in rows.items()})
with open('sample-rows.tsv', 'w') as a, open('sample-key.tsv', 'w') as b:
    for i, (p, s, t) in enumerate(out):
        a.write(f'{i}\t{p}\t{s}\n'); b.write(f'{i}\t{p}\t{s}\t{t}\n')
