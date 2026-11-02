#!/usr/bin/env python3
"""Second blind sample: the named tier, chosen after the first sample, tested on fresh rows."""
import json, random
d = json.load(open('star-map.json'))
old = {tuple(l.rstrip('\n').split('\t')[1:3]) for l in open('sample-key.tsv')}
rows = sorted((p, s) for p, ts in d['tags'].items() for s, t in ts if t == 'named' and (p, s) not in old)
print(len(rows))
r = random.Random(11).sample(rows, 25)
with open('sample2-rows.tsv', 'w') as f:
    for i, (p, s) in enumerate(r):
        f.write(f'{i}\t{p}\t{s}\n')
