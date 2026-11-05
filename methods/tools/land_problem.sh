#!/bin/bash
# land_problem.sh P: blueprint has 0 sorry -> verify, copy to Main.lean, status, registry, commit.
p=$1; cd ~/worktrees/apm-lean/lemmas || exit 1
B=holes/labs/blueprints/$p/Blueprint.lean; M=problems/$p/lean/Main.lean
[ "$(grep -cE '^\s*sorry\s*$' $B)" = 0 ] || { echo "$p still has sorry"; exit 1; }
cp $B $M
# Guard (2026-10-13): Blueprint text may differ in layout from the registered statement
# (t97A07: a reflowed def broke the fingerprint; master had to restore the spacing).
python3 scripts/statement-registry.py check $p --rev "" 2>&1 | grep -qE "^1 registered statements match|unregistered" || {
  echo "registry mismatch after copying the blueprint: restore the registered statement text in $B"; git checkout -q -- $M; exit 1; }
d=$(python3 -c "import json;e=json.load(open('problems/STATEMENTS.json'))['entries'].get('$p');print(' '.join(e['decls']) if e else 'apm_'+'$p'.lower())")
mkdir -p holes/labs/lemmas/$p; f=holes/labs/lemmas/$p/main.check.lean; (cat $M; echo; for x in $d; do echo "#print axioms $x"; done) > $f
out=$(systemd-run --user --scope -q -p MemoryMax=12G lake env lean $f 2>&1); rm $f
echo "$out" | grep -q ": error" && { echo "$out" | grep ": error" | head -3; git checkout -q -- $M; exit 1; }
echo "$out" | grep -q "depends on axioms" || { echo "no axiom output: check did not run"; git checkout -q -- $M; exit 1; }
ax=$(echo "$out" | tr -s ' \n' ' ' | grep -o "depends on axioms: \[[^]]*\]" | sort -u); echo "$ax"
echo "$ax" | grep -q sorryAx && { echo "sorryAx!"; git checkout -q -- $M; exit 1; }
# 11-01: also refuse native_decide axioms, which sorryAx alone misses.
echo "$ax" | grep -q "_native" && { echo "native_decide axiom!"; git checkout -q -- $M; exit 1; }
python3 - $p <<'P'
import json,sys;p=f'problems/{sys.argv[1]}/status.json'
try:
  d=json.load(open(p));l=d.get('lean',{})
  if 'sorry_count_main' in l: l['sorry_count_main']=0; l['sorry_count_total']=0
  json.dump(d,open(p,'w'),indent=2,ensure_ascii=False); open(p,'a').write('\n')
except FileNotFoundError: pass
P
reg=$(python3 scripts/statement-registry.py status $p)
git add problems/$p && git commit -qm "$p: closed — all blueprint lemmas proved (parallel lemma rounds); registry: $reg

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>" && git log --oneline -1
echo "registry: $reg"; echo "
$p CLOSED ($(date -u +%H:%MZ)); registry $reg" >> ~/notes/packets/lemmas/STATUS.md
# Merge to master and push (Joe 2026-10-23); merge_lemmas.sh says what it checks.
~/notes/packets/lemmas/merge_lemmas.sh || echo "$p closed on lemmas but NOT merged to master (see above)"
