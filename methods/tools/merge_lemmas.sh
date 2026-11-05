#!/bin/bash
# merge_lemmas.sh: merge the lemmas branch into master and push (Joe 2026-10-23: land_problem.sh
# should do this, with the checks that were being done by hand). Called at the end of
# land_problem.sh; also runs alone. Exit 0 = merged and pushed (or nothing to merge).
#
# What it checks, in order, and why:
#  1. The main checkout is on master with no tracked changes, and origin/master is contained in
#     master. Other seats (topology loop) commit to master there; we never rebase or pull.
#  2. The merge is made on a scratch branch in its own worktree, so a conflict or a failed build
#     never touches master. (10-23: t98A02 was merged this way, then master fast-forwarded.)
#  3. Paths outside holes/labs/, problems/ and the lean_lib directories, or a changed
#     lake-manifest.json / lakefile, stop the merge for a person to look at.
#  4. Statement registry check for every problem whose Main.lean the merge changes.
#  5. Build, only when a Lean module (a lean_lib file) changed on either side since the merge
#     base: lake build those modules, then compile each changed Main.lean and refuse on an error
#     or sorryAx. When no module changed, land_problem.sh's check ran against the same imports,
#     so it is not repeated (10-23: t93A03 was merged without a build for this reason).
#  6. master is fast-forwarded to the checked merge commit and pushed; the scratch worktree and
#     branch are removed; closed-to-merge.txt is cleared and STATUS.md gets a line.
# The merge message has a body and a trailer block, so the signing hook appends its trailers
# there (a one-line -m message got Agent-Session glued onto the subject in feefdc677).
set -o pipefail
MAIN=/home/joe/code/apm-lean; L=~/notes/packets/lemmas; BR=${BR:-lemmas}
# CHECK_ONLY=1: do steps 1-5, then drop the scratch merge (for testing the checks).
cd $MAIN || exit 1
exec 8>/tmp/apm-lemmas-merge.lock; flock -n 8 || { echo "merge_lemmas: another merge is running"; exit 1; }

# 1. main checkout state
[ "$(git symbolic-ref --short HEAD)" = master ] || { echo "merge_lemmas: $MAIN is not on master"; exit 1; }
git diff --quiet HEAD || { echo "merge_lemmas: $MAIN has uncommitted tracked changes (another seat?): not merged"; git status --short -uno | head; exit 1; }
git fetch -q origin master || { echo "merge_lemmas: fetch failed"; exit 1; }
git merge-base --is-ancestor origin/master master || {
  echo "merge_lemmas: origin/master has commits master lacks: reconcile by hand (no pull here)"; exit 1; }
tip=$(git rev-parse $BR)
git merge-base --is-ancestor $tip master && { echo "merge_lemmas: $BR already in master"; exit 0; }
base=$(git merge-base master $tip)

# 3. what the merge brings in
libs=$(sed -n '/^\[\[lean_lib\]\]/,/^name/ s/^name *= *"\(.*\)"/\1/p' lakefile.toml)
libre="^($(echo $libs | tr ' ' '|'))/"
incoming=$(git diff --name-only master...$tip)
odd=$(echo "$incoming" | grep -vE "^(holes/labs/|problems/)" | grep -vE "$libre")
[ -n "$odd" ] && { echo "merge_lemmas: $BR changes paths outside holes/labs, problems and the lean libs:"; echo "$odd" | head -20; echo "not merged"; exit 1; }
probs=$(echo "$incoming" | sed -nE 's#^problems/([^/]+)/lean/Main\.lean$#\1#p' | sort -u)
mods=$( { git diff --name-only $base master; echo "$incoming"; } | grep -E "$libre" | grep '\.lean$' | sort -u | sed 's#\.lean$##; s#/#.#g')
echo "merge_lemmas: $(echo "$incoming" | wc -l) files; problems: ${probs:-none}; modules to build: ${mods:-none}"

# 2. scratch merge
stamp=$(date -u +%m%d-%H%M%S); W=~/worktrees/apm-lean/merge-lemmas-$stamp; S=merge-lemmas-$stamp
cleanup() { cd $MAIN; git worktree remove --force $W 2>/dev/null; git branch -qD $S 2>/dev/null; }
git worktree add -q -b $S $W master || exit 1
cd $W; mkdir -p .lake; ln -s $MAIN/.lake/packages .lake/packages
# 11-01: a statement-only merge (ALLOW_SORRY) is not a closure, so it is not called one.
cl=$(for p in $probs; do case " $ALLOW_SORRY " in *" $p "*) ;; *) echo $p;; esac; done)
subj="Merge branch '$BR': ${cl:+$(echo $cl) closed}"; [ -n "$cl" ] || subj="Merge branch '$BR': lemma rounds"
msg=$(mktemp); printf '%s\n\nlemmas %s; checked by merge_lemmas.sh (registry%s).\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' \
  "$subj" "${tip:0:9}" "${mods:+, lake build, Main.lean axioms}" > $msg
git merge -q --no-ff --no-edit -F $msg $tip || { echo "merge_lemmas: conflict merging $BR"; git diff --name-only --diff-filter=U | head; git merge --abort; rm $msg; cleanup; exit 1; }
rm $msg

# 4. registry
for p in $probs; do
  r=$(python3 scripts/statement-registry.py check $p 2>&1)
  echo "$r" | grep -qE "^1 registered statements match|unregistered" || { echo "merge_lemmas: registry check failed for $p:"; echo "$r" | tail -5; cleanup; exit 1; }
done

# 5. build when a module changed (modules deleted by the merge are not built)
# Also build the lean_lib modules each merged Main.lean imports: one that reached master in an
# earlier merge is not in the diff, and $MAIN/.lake/build need not have it (10-25: t96A01 and
# t00A02 failed on a missing StandardSurfaceFiniteCover.olean after t94J04's merge).
imps=$(for p in $probs; do sed -nE 's/^import +([^ ]+).*/\1/p' problems/$p/lean/Main.lean; done | grep -E "^($(echo $libs | tr ' ' '|'))\." )
mods=$(echo $mods $imps | tr ' ' '\n' | sort -u)
mods=$(for x in $mods; do [ -f "$(echo $x | tr . /).lean" ] && echo $x; done)
if [ -n "$mods" ]; then
  cp -a $MAIN/.lake/build .lake/build
  out=$(flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=12G lake build $mods 2>&1) || {
    echo "merge_lemmas: lake build failed:"; echo "$out" | grep -E "error" | head -5; cleanup; exit 1; }
  for p in $probs; do
    M=problems/$p/lean/Main.lean; f=$(mktemp --suffix=.lean -p problems/$p/lean)
    d=$(python3 -c "import json;e=json.load(open('problems/STATEMENTS.json'))['entries'].get('$p');print(' '.join(e['decls']) if e else 'apm_'+'$p'.lower())")
    (cat $M; echo; for x in $d; do echo "#print axioms $x"; done) > $f
    out=$(flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=12G lake env lean $f 2>&1); rm $f
    echo "$out" | grep -q ": error" && { echo "merge_lemmas: $M fails on the merged tree:"; echo "$out" | grep ": error" | head -3; cleanup; exit 1; }
    echo "$out" | grep -q "depends on axioms" || { echo "merge_lemmas: no axiom output for $p"; cleanup; exit 1; }
    case " $ALLOW_SORRY " in *" $p "*) ;; *) echo "$out" | grep -q sorryAx && { echo "merge_lemmas: sorryAx in $p"; cleanup; exit 1; };; esac
  done
fi

[ -n "$CHECK_ONLY" ] && { echo "merge_lemmas: CHECK_ONLY: checks passed for $(git rev-parse --short HEAD); not merged"; cleanup; exit 0; }

# 6. fast-forward, push, tidy
m=$(git rev-parse HEAD); cd $MAIN
git merge -q --ff-only $m || { echo "merge_lemmas: master moved or the checkout blocks the fast-forward: merge $m is on $S"; exit 1; }
cleanup
git push -q origin master || { echo "merge_lemmas: push failed; master is at $(git log --oneline -1)"; exit 1; }
git log --oneline -1
: > $L/closed-to-merge.txt
echo "
$(date -u +%Y-%m-%dT%H:%MZ) lemmas merged to master ($(git rev-parse --short HEAD)) by merge_lemmas.sh: ${probs:-no problems}" >> $L/STATUS.md
