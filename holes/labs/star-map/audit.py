#!/usr/bin/env python3
"""Compile every registered problem's Main.lean and record errors and axioms of its decls.
Writes holes/labs/star-map/compile-audit.tsv: id, error count, status, first error."""
import json, os, re, subprocess, tempfile, concurrent.futures as cf
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
reg = json.load(open(os.path.join(ROOT, 'problems/STATEMENTS.json')))['entries']
def run(pid):
    src = os.path.join(ROOT, 'problems', pid, 'lean', 'Main.lean')
    try:
        p = subprocess.run(['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=14G', 'nice', '-n', '15',
                            'lake', 'env', 'lean', src], cwd=ROOT, capture_output=True, text=True, timeout=2400)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return pid, -1, 'timeout', ''
    errs = [l for l in out.splitlines() if re.search(r':\d+:\d+: error', l)]
    sorry = sum(1 for l in out.splitlines() if 'declaration uses' in l and 'sorry' in l)
    return pid, len(errs), f'sorry-warnings={sorry}', (errs[0][-140:] if errs else '')
with cf.ThreadPoolExecutor(5) as ex, open(os.path.join(ROOT, 'holes/labs/star-map/compile-audit.tsv'), 'w') as f:
    for r in ex.map(run, sorted(reg)):
        f.write('\t'.join(map(str, r)) + '\n'); f.flush()
