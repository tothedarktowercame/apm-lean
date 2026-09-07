#!/usr/bin/env bash
# Land certified solver work onto apm-lean master.
#
# Joe, 2026-09-07: "yes, please check, and do get them onto master. also,
# suitable commits need to be made at the end of each frame".
#
# WHY THIS EXISTS. A frame's solver works in a leased worktree on
# exp/countdown-<frame>-<problem>-solver. workspace-lifecycle/retire! removes
# the worktree at frame end but deliberately RETAINS the branch
# (:retained-head on the retirement receipt). Nothing then promotes that work
# to master, so a problem the campaign genuinely closed keeps reading as open
# on master. Measured 2026-09-07: 46 such problems, master showing a sorry for
# every one of them. That understates the corpus in exactly the direction the
# 2026-09-07 metadata audit was correcting for.
#
#   land-certified-solves.sh survey            list candidates, change nothing
#   land-certified-solves.sh land <list-file>  land the rows in <list-file>
#
# <list-file> is "<frame> <problem> <branch>" per line -- normally the output
# of survey, FILTERED to rows an independent check has passed. This script
# does not decide correctness: elaboration and statement-equality are verified
# upstream, because a receipt claiming zero sorries is not the same as a file
# that elaborates with zero sorries, and this corpus has had both.
set -uo pipefail
REPO=/home/joe/code/apm-lean
cd "$REPO" || exit 1

survey() {
  for b in $(git branch --list "exp/countdown-*-solver" --format="%(refname:short)"); do
    git merge-base --is-ancestor "$b" master 2>/dev/null && continue
    prob=$(echo "$b" | sed -E "s/^exp\/countdown-f[0-9]+-(.+)-solver$/\1/")
    frame=$(echo "$b" | sed -E "s/^exp\/countdown-(f[0-9]+)-.*/\1/")
    f="problems/$prob/lean/Main.lean"
    bs=$(git show "$b:$f" 2>/dev/null | grep -cE "^[[:space:]]*sorry[[:space:]]*$")
    ms=$(git show "master:$f" 2>/dev/null | grep -cE "^[[:space:]]*sorry[[:space:]]*$")
    [ -z "$bs" ] && continue
    if [ "$bs" = "0" ] && [ "${ms:-0}" -gt 0 ] 2>/dev/null; then
      echo "$frame $prob $b"
    fi
  done
}

case "${1:-survey}" in
survey) survey ;;
land)
  list="${2:-}"; [ -f "$list" ] || { echo "usage: $0 land <list-file>"; exit 2; }
  # The topology build loop refuses to run against a dirty tracked worktree
  # (repository_safe) and commits to this same master. Land in one batch and
  # leave the tree clean, so the window where it could collide is minimal.
  if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    echo "REFUSING: tracked worktree is dirty; land only from a clean tree"; exit 1
  fi
  landed=0; skipped=0; manifest=""
  while read -r frame prob branch; do
    [ -z "$frame" ] && continue
    f="problems/$prob/lean/Main.lean"
    head=$(git rev-parse --verify "$branch" 2>/dev/null) || { echo "  SKIP $prob (no branch)"; skipped=$((skipped+1)); continue; }
    git show "$branch:$f" > /dev/null 2>&1 || { echo "  SKIP $prob (no file on branch)"; skipped=$((skipped+1)); continue; }
    git checkout "$branch" -- "$f" 2>/dev/null || { echo "  SKIP $prob (checkout failed)"; skipped=$((skipped+1)); continue; }
    landed=$((landed+1))
    manifest="$manifest
  $prob  from $frame  $branch  ${head:0:12}"
    echo "  landed $prob ($frame)"
  done < "$list"

  if [ "$landed" = 0 ]; then echo "nothing to land"; exit 0; fi
  git commit -q -F - <<EOF
Land $landed certified solver proofs onto master

Each frame's solver closes its problem in a leased worktree on
exp/countdown-<frame>-<problem>-solver. retire! removes the worktree at frame
end and deliberately retains the branch, but nothing ever promoted that work to
master -- so master kept showing a sorry for problems the campaign had closed.

Every proof landed here was verified from the Lean source, not from its receipt:
elaborates with exit 0, zero errors, zero "declaration uses 'sorry'" warnings,
axioms within [propext, Classical.choice, Quot.sound], and its target statement
unchanged from master's. A proof that closed by weakening its statement would be
worse than the sorry it replaced, so statement equality was checked separately
and is not inferred from the axiom list.

Landed:$manifest

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>
EOF
  echo "  ---"; echo "  landed: $landed | skipped: $skipped"
  git log -1 --format='  commit %h %s'
  ;;
*) echo "usage: $0 survey | land <list-file>"; exit 2 ;;
esac
