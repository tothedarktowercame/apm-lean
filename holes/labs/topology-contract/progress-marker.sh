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
set -uo pipefail
LEAN=/home/joe/code/apm-lean
LAB="$LEAN/holes/labs/topology-contract"
OUT="${TOPOLOGY_RUNS:-$LAB/runs}/progress-baseline.json"
# The ledger has to move with the run directory. Parameterizing only OUT would
# write a runs2 baseline holding the FIRST campaign's row counts, which is a
# progress report about the wrong campaign.
LEDGER="${TOPOLOGY_LEDGER:-$LAB/worklist.edn}"

snapshot() {
python3 - "$LEAN" "$LEDGER" <<'PY'
import json, os, glob, subprocess, sys, datetime
root=sys.argv[1]; os.chdir(root)
stems=[os.path.splitext(os.path.basename(f))[0] for f in glob.glob('apm/*.tex')]
bundles=[s for s in stems if os.path.isdir(f'problems/{s}')]
def has_lean(s):
    d=f'problems/{s}/lean'
    return os.path.isdir(d) and any(x.endswith('.lean') for r,_,fs in os.walk(d) for x in fs)
lean=[s for s in bundles if has_lean(s)]
solved=open_=0; t_solved=t_open=0; informal_only=0
# Count formalization progress over LEAN-BEARING bundles only. sorry_count_total
# is 0 for a problem with no Lean at all -- lean.main null, files [] -- so
# iterating every bundle counted 31 informal-only problems (a98J05, t99J02,
# t95A01, ...) as SOLVED on 2026-09-07, reporting 343 where 312 are formalized.
# The `lean` list above was already computed and then not used here.
# The 31 are still reported, as informal_only, so nothing is hidden by the fix.
for s in bundles:
    if not has_lean(s):
        p2=f'problems/{s}/status.json'
        if os.path.exists(p2):
            try:
                if (json.load(open(p2)).get('lean',{}) or {}).get('sorry_count_total')==0:
                    informal_only+=1
            except Exception: pass
        continue
    p=f'problems/{s}/status.json'
    if not os.path.exists(p): continue
    try: n=json.load(open(p)).get('lean',{}).get('sorry_count_total')
    except Exception: continue
    if n is None: continue
    if n==0:
        solved+=1
        if s.startswith('t'): t_solved+=1
    else:
        open_+=1
        if s.startswith('t'): t_open+=1
def sh(*a):
    try: return subprocess.run(a,capture_output=True,text=True,timeout=60).stdout.strip()
    except Exception: return ''
wl={}
try:
    ledger=sys.argv[2] if len(sys.argv)>2 else root+'/holes/labs/topology-contract/worklist.edn'
    txt=sh('bb','-e','(let [w (read-string (slurp "%s"))] (prn {:items (count (:items w)) :states (frequencies (map :state (:items w)))}))'%ledger)
    wl=txt
except Exception: pass
print(json.dumps({
  'at': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
  'apm_lean_head': sh('git','-C',root,'rev-parse','--short','HEAD'),
  'apm_lean_commits': sh('git','-C',root,'rev-list','--count','HEAD'),
  'stems': len(stems), 'bundles': len(bundles),
  'with_lean': len(lean), 'solved': solved, 'open': open_,
  'informal_only': informal_only,
  'topology_solved': t_solved, 'topology_open': t_open,
  'construction_targets_lean': len(glob.glob('ConstructionTargets/*.lean')),
  'construction_targets_md': len(glob.glob('ConstructionTargets/*.md')),
  'worklist': wl,
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
    NOW=$(snapshot)
    python3 - "$OUT" <<PY
import json,sys
base=json.load(open(sys.argv[1]))
now=json.loads('''$NOW''')
print(f"TOPOLOGY CAMPAIGN PROGRESS")
print(f"  baseline {base['at']}")
print(f"  now      {now['at']}\n")
keys=[('solved','problems SOLVED (Lean)'),('open','problems open'),
      ('informal_only','informal-only (no Lean)'),
      ('with_lean','problems with Lean'),('bundles','bundles'),
      ('topology_solved','topology solved'),('topology_open','topology open'),
      ('construction_targets_lean','construction targets (.lean)'),
      ('construction_targets_md','construction targets (.md)'),
      ('apm_lean_commits','apm-lean commits')]
# A baseline taken before 2026-09-07 counted every bundle at zero sorries as
# SOLVED, including 31 informal-only problems with no Lean file at all. Those
# are now counted separately, so a pre-change baseline shows solved and
# topology_solved DROPPING. That is the correction landing, not work lost, and
# saying so beats letting a reader infer a regression.
if 'informal_only' not in base:
    print("  NOTE: baseline predates the solved-count fix; SOLVED and topology")
    print("        solved drop by the informal-only problems they used to")
    print("        include. That is a definition correction, not lost work.\n")
moved=False
for k,label in keys:
    b,n=base.get(k),now.get(k)
    try: d=int(n)-int(b)
    except Exception: continue
    flag=''
    if d: moved=True; flag=f"   <-- {d:+d}"
    print(f"  {label:<32} {b:>6} -> {n:>6}{flag}")
print(f"\n  worklist baseline: {base.get('worklist')}")
print(f"  worklist now     : {now.get('worklist')}")
print(f"\n  HEAD {base.get('apm_lean_head')} -> {now.get('apm_lean_head')}")
print("\n  " + ("MOVEMENT DETECTED" if moved else "NO NUMERIC CHANGE since baseline"))
PY
    ;;
  *) echo "usage: $0 [baseline|report]"; exit 2 ;;
esac
