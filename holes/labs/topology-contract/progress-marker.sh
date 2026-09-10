#!/usr/bin/env bash
# Topology campaign progress marker.
#
#   progress-marker.sh baseline   -- write runs/progress-baseline.json (once)
#   progress-marker.sh report     -- print what changed since the baseline
#
# Written 2026-09-06 21:45Z, right after the owner-authorization gate was
# withdrawn (apm-lean 96a39230) and the build loop restarted.  The point is
# that Joe can walk away and, on return, see whether the loop actually moved
# anything rather than merely stayed alive.
#
# Solved/open are counted from the Lean files themselves, not from
# problems/*/status.json.  Nothing in the build loop refreshes status.json:
# on 2026-09-10 it still carried its 2026-09-06 counts, so nine topology
# problems closed since then (t00A01, t94J08, t96J07, ...) read as open, while
# 17 informal-only bundles whose Main.lean is a bare statement with one
# `sorry` read as solved.  The report lists every status.json that disagrees
# with the files, so the staleness stays visible.
set -uo pipefail
LEAN=/home/joe/code/apm-lean
LAB="$LEAN/holes/labs/topology-contract"
OUT="${TOPOLOGY_RUNS:-$LAB/runs}/progress-baseline.json"
# The ledger has to move with the run directory. Parameterizing only OUT would
# write a runs2 baseline holding the FIRST campaign's row counts, which is a
# progress report about the wrong campaign.
LEDGER="${TOPOLOGY_LEDGER:-$LAB/worklist.edn}"

# snapshot [COMMIT] -- counts for the working tree, or for COMMIT read via git.
snapshot() {
python3 - "$LEAN" "$LEDGER" "${1:-}" <<'PY'
import json, os, re, subprocess, sys, datetime
root, ledger, commit = sys.argv[1], sys.argv[2], sys.argv[3] or None
os.chdir(root)

def sh(*a):
    try: return subprocess.run(a, capture_output=True, text=True, timeout=120).stdout.strip()
    except Exception: return ''

# File access: the working tree, or a commit through one `git cat-file --batch`.
if commit:
    paths = sh('git', 'ls-tree', '-r', '--name-only', commit, '--',
               'apm', 'problems', 'ConstructionTargets').splitlines()
    want = [p for p in paths if p.startswith('problems/')
            and (p.endswith('.lean') and '/lean/' in p or p.endswith('/status.json'))]
    proc = subprocess.run(['git', 'cat-file', '--batch'], capture_output=True,
                          input=''.join(f'{commit}:{p}\n' for p in want).encode())
    blob, buf, pos = {}, proc.stdout, 0
    for p in want:
        nl = buf.index(b'\n', pos); header = buf[pos:nl].split()
        if len(header) < 3 or header[1] != b'blob': pos = nl + 1; continue
        size = int(header[2]); blob[p] = buf[nl+1:nl+1+size].decode('utf-8', 'replace')
        pos = nl + 1 + size + 1
    read = blob.get
else:
    paths = []
    for top in ('apm', 'problems', 'ConstructionTargets'):
        for r, _, fs in os.walk(top):
            paths.extend(os.path.join(r, f) for f in fs)
    def read(p):
        try: return open(p, encoding='utf-8', errors='replace').read()
        except OSError: return None

# Placeholders outside comments and string literals: `sorry`, `admit`, and
# top-level `axiom` declarations (the same forbidden set the loop scans for).
TOK0 = re.compile(r'--|/-|"|\'"\'')
TOKC = re.compile(r'/-|-/')
PH = re.compile(r'(?<![\w.])(?:sorry|admit)(?![\w.])')
AX = re.compile(r'(?m)^[ \t]*(?:private[ \t]+|protected[ \t]+)?axiom[ \t]')
def placeholders(src):
    code, i, n = [], 0, len(src)
    while i < n:
        m = TOK0.search(src, i)
        if not m: code.append(src[i:]); break
        code.append(src[i:m.start()]); t = m.group(); i = m.end()
        if t == '--':
            j = src.find('\n', i); i = n if j < 0 else j
        elif t == '"':
            while i < n and src[i] != '"': i += 2 if src[i] == '\\' else 1
            i += 1
        elif t == '/-':
            depth = 1
            while depth and i < n:
                m2 = TOKC.search(src, i)
                if not m2: i = n; break
                depth += 1 if m2.group() == '/-' else -1; i = m2.end()
    c = ''.join(code)
    return len(PH.findall(c)) + len(AX.findall(c))

stems = sorted(os.path.splitext(os.path.basename(p))[0] for p in paths
               if p.startswith('apm/') and p.count('/') == 1 and p.endswith('.tex'))
lean_files, bundles = {}, set()
for p in paths:
    parts = p.split('/')
    if parts[0] == 'problems' and len(parts) > 2:
        bundles.add(parts[1])
        if parts[2] == 'lean' and p.endswith('.lean'):
            lean_files.setdefault(parts[1], []).append(p)
bundles = [s for s in stems if s in bundles]

solved, open_, no_lean, stubs, stale = [], [], [], [], []
for s in bundles:
    try: st = json.loads(read(f'problems/{s}/status.json') or '{}')
    except ValueError: st = {}
    recorded = (st.get('lean') or {}).get('sorry_count_total')
    if s not in lean_files: no_lean.append(s); continue
    n = sum(placeholders(read(p) or '') for p in lean_files[s])
    (solved if n == 0 else open_).append(s)
    if n and st.get('classification') == 'informal-only': stubs.append(s)
    if recorded is not None and (recorded == 0) != (n == 0):
        stale.append({'id': s, 'status_json': recorded, 'files': n})

wl = sh('bb', '-e', '(let [w (read-string (slurp "%s"))] (prn {:items (count (:items w)) :states (frequencies (map :state (:items w)))}))' % ledger)
ref = commit or 'HEAD'
topo = lambda xs: [s for s in xs if s.startswith('t')]
print(json.dumps({
  'method': 'lean-files',
  'at': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
  'apm_lean_head': sh('git', 'rev-parse', '--short', ref),
  'apm_lean_commits': sh('git', 'rev-list', '--count', ref),
  'stems': len(stems), 'bundles': len(bundles),
  'with_lean': len(solved) + len(open_), 'solved': len(solved), 'open': len(open_),
  'open_stub': len(stubs), 'informal_only': len(no_lean),
  'topology_solved': len(topo(solved)), 'topology_open': len(topo(open_)),
  'construction_targets_lean': sum(1 for p in paths if p.startswith('ConstructionTargets/') and p.count('/') == 1 and p.endswith('.lean')),
  'construction_targets_md': sum(1 for p in paths if p.startswith('ConstructionTargets/') and p.count('/') == 1 and p.endswith('.md')),
  'worklist': wl,
  'solved_ids': solved,
  'stale_status': stale,
}, indent=2))
PY
}

case "${1:-report}" in
  baseline)
    # "(once)" was a comment, not a guard, and this silently overwrote a
    # baseline taken on 2026-09-06 when it was run to test an unrelated change
    # on 2026-09-09. A baseline's whole value is being older than the thing it
    # measures, and runs/ is gitignored, so an overwrite is unrecoverable.
    if [ -f "$OUT" ] && [ "${2:-}" != --force ]; then
      echo "baseline already exists: $OUT" >&2
      echo "taken $(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["at"])' "$OUT" 2>/dev/null || echo unknown)" >&2
      echo "re-run with: $0 baseline --force   (this discards the older reference point)" >&2
      exit 1
    fi
    snapshot > "$OUT"; echo "baseline written: $OUT"; cat "$OUT" ;;
  report)
    [ -f "$OUT" ] || { echo "no baseline; run: $0 baseline"; exit 1; }
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    snapshot > "$tmp/now.json"
    # A baseline written before counting moved to the Lean files holds
    # status.json numbers. Recount it the new way at the commit it recorded,
    # so both columns use one definition; its own time and worklist are kept.
    recount=$(python3 -c 'import json,sys;b=json.load(open(sys.argv[1]));print("" if b.get("method")=="lean-files" else b.get("apm_lean_head",""))' "$OUT")
    if [ -n "$recount" ]; then snapshot "$recount" > "$tmp/base.json"; else cp "$OUT" "$tmp/base.json"; fi
    python3 - "$OUT" "$tmp/base.json" "$tmp/now.json" "$LEAN" <<'PY'
import json, subprocess, sys
stored, base, now = (json.load(open(p)) for p in sys.argv[1:4]); root = sys.argv[4]
recounted = stored.get('method') != 'lean-files'
if recounted: base['at'], base['worklist'] = stored['at'], stored.get('worklist')
print("TOPOLOGY CAMPAIGN PROGRESS")
print(f"  baseline {base['at']}")
print(f"  now      {now['at']}\n")
if recounted:
    print(f"  NOTE: the stored baseline was counted from status.json; it has been")
    print(f"        recounted from the Lean files at its commit {stored.get('apm_lean_head')}.")
    print(f"        (status.json then said {stored.get('solved')} solved, {stored.get('topology_solved')} topology.)\n")
keys=[('solved','problems SOLVED (Lean, 0 placeholders)'),('open','problems open (Lean)'),
      ('open_stub','  of which statement-only stubs'),
      ('informal_only','informal-only (no Lean)'),
      ('with_lean','problems with Lean'),('bundles','bundles'),
      ('topology_solved','topology solved'),('topology_open','topology open'),
      ('construction_targets_lean','construction targets (.lean)'),
      ('construction_targets_md','construction targets (.md)'),
      ('apm_lean_commits','apm-lean commits')]
moved=False
for k,label in keys:
    b,n=base.get(k),now.get(k)
    try: d=int(n)-int(b)
    except Exception: continue
    flag=''
    if d: moved=True; flag=f"   <-- {d:+d}"
    print(f"  {label:<38} {b:>6} -> {n:>6}{flag}")
def when(s):
    return subprocess.run(['git','-C',root,'log','-1','--format=%ad %h','--date=format:%m-%d %H:%M','--',f'problems/{s}/lean'],
                          capture_output=True,text=True).stdout.strip()
closed=sorted(set(now['solved_ids'])-set(base['solved_ids']))
reopened=sorted(set(base['solved_ids'])-set(now['solved_ids']))
if closed:
    print(f"\n  closed since baseline ({len(closed)}):")
    for s in sorted(closed,key=when,reverse=True): print(f"    {s:<8} {when(s)}")
if reopened:
    print(f"\n  REOPENED since baseline ({len(reopened)}): {' '.join(reopened)}")
stale=now.get('stale_status') or []
if stale:
    print(f"\n  status.json disagrees with the Lean files for {len(stale)} bundles (files win):")
    print("    " + ' '.join(f"{x['id']}({x['status_json']}->{x['files']})" for x in stale))
print(f"\n  worklist baseline: {base.get('worklist')}")
print(f"  worklist now     : {now.get('worklist')}")
print(f"\n  HEAD {base.get('apm_lean_head')} -> {now.get('apm_lean_head')}")
print("\n  " + ("MOVEMENT DETECTED" if moved else "NO NUMERIC CHANGE since baseline"))
PY
    ;;
  *) echo "usage: $0 [baseline|report]"; exit 2 ;;
esac
