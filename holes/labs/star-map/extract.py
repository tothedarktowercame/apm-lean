#!/usr/bin/env python3
"""Dump the Mathlib constants each APM proof reaches, for the prelim star map.

For each problem, append a small Lean command to a copy of Main.lean that walks
the main theorem through declarations local to the file and prints every
non-local constant it touches, with its Mathlib module and kind.  Output goes to
holes/labs/star-map/deps/<id>.tsv, one DEP line per constant; a file holding
ERROR means the run failed.  Usage: extract.py [-j N] [ids...]  (default: every
registered problem without a dump).
"""
import json, os, subprocess, sys, tempfile, concurrent.futures as cf
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
HERE = os.path.join(ROOT, 'holes/labs/star-map')
OUT = os.path.join(HERE, 'deps')
args = sys.argv[1:]
jobs = 4
if args[:1] == ['-j']:
    jobs = int(args[1]); args = args[2:]
reg = json.load(open(os.path.join(ROOT, 'problems/STATEMENTS.json')))['entries']
ids = args or sorted(reg)
tail = open(os.path.join(HERE, 'DepDump.lean.txt')).read()
os.makedirs(OUT, exist_ok=True)

def run(pid):
    dest = os.path.join(OUT, pid + '.tsv')
    if os.path.exists(dest) and not args:
        return pid, 'skip'
    decls = reg[pid].get('decls') or []
    src = os.path.join(ROOT, 'problems', pid, 'lean', 'Main.lean')
    tmp = tempfile.NamedTemporaryFile('w', suffix='.lean', dir=os.path.join(ROOT, 'scratch'), delete=False)
    lines = open(src).read().splitlines()
    k = max((i for i, l in enumerate(lines) if l.startswith('import ')), default=-1) + 1
    tmp.write('import Lean\n' + '\n'.join(lines[:k]) + '\n' + tail + '\n' + '\n'.join(lines[k:]) +
              '\n#star_map_deps ' + ' '.join(decls) + '\n')
    tmp.close()
    try:
        p = subprocess.run(['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=14G', 'nice', '-n', '15',
                            'lake', 'env', 'lean', tmp.name], cwd=ROOT, capture_output=True, text=True, timeout=1800)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        out = 'ERROR timeout'
    finally:
        os.unlink(tmp.name)
    deps = [l for l in out.splitlines() if l.startswith('DEP\t')]
    errs = [l for l in out.splitlines() if ' error' in l or l.startswith('ERROR')]
    with open(dest, 'w') as f:
        if not deps:
            f.write('ERROR\n' + '\n'.join(errs[:5]) + '\n')
        else:
            f.write("\n".join(deps) + "\n")
    return pid, len(deps)

with cf.ThreadPoolExecutor(jobs) as ex:
    for pid, r in ex.map(run, ids):
        print(pid, r, flush=True)
