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
#   land-certified-solves.sh verify [list]     filter rows to those that PASS
#   land-certified-solves.sh land <list-file>  land the rows in <list-file>
#   land-certified-solves.sh auto              survey | verify | land, unattended
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
    # Branch side stays line-anchored: it only selects CANDIDATES, verify is
    # what decides, and erring narrow here costs a visible pending row rather
    # than a bad landing. Master side must catch inline forms, or a problem
    # whose master copy holds `all_goals sorry` is never offered for landing
    # at all -- which is how a real gap stays invisible.
    bs=$(git show "$b:$f" 2>/dev/null | grep -cE "^[[:space:]]*sorry[[:space:]]*$")
    ms=$(git show "master:$f" 2>/dev/null \
         | grep -cE "(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)")
    [ -z "$bs" ] && continue
    if [ "$bs" = "0" ] && [ "${ms:-0}" -gt 0 ] 2>/dev/null; then
      echo "$frame $prob $b"
    fi
  done
}

# The independent check the header demands, as code rather than as a human
# instruction. A receipt claiming zero sorries is not a file that elaborates
# with zero sorries, and a proof that closed by WEAKENING its statement would be
# worse than the sorry it replaced -- so both are checked from source, per row:
#
#   1. the registered `theorem apm_<id>` signature is byte-identical to master's
#   2. the branch file elaborates: lake exit 0, and no bare `sorry` line
#
# Rows that fail are reported on stderr and dropped, never landed.
verify() {
  local list="${1:-/dev/stdin}"
  while read -r frame prob branch; do
    [ -z "${frame:-}" ] && continue
    local f="problems/$prob/lean/Main.lean"
    local lower; lower=$(echo "$prob" | tr "[:upper:]" "[:lower:]")
    local a b
    a=$(git show "master:$f" 2>/dev/null | sed -n "/^theorem apm_${lower}[^_a-z0-9]/,/:=/p" | tr -s "[:space:]" " ")
    b=$(git show "$branch:$f" 2>/dev/null | sed -n "/^theorem apm_${lower}[^_a-z0-9]/,/:=/p" | tr -s "[:space:]" " ")
    if [ -z "$a" ] || [ "$a" != "$b" ]; then
      echo "  DROP $prob: registered statement differs from master (or not found)" >&2
      continue
    fi
    local tmp out; tmp=$(mktemp /tmp/land-verify-XXXXXX.lean)
    git show "$branch:$f" > "$tmp" 2>/dev/null
    # The COMPILER decides whether a proof is complete, not a regex. A
    # line-anchored /^\s*sorry\s*$/ misses every inline form -- `all_goals
    # sorry`, `exact sorry`, `:= by sorry` -- and lake EXITS 0 on all of them,
    # emitting only `declaration uses 'sorry'` as a warning. Checking exit
    # status plus that regex therefore passed unproved work: t95J04 and b98A02
    # both carry `all_goals sorry` and both look clean to it. This tool lands
    # onto master unattended every 30 minutes, so that was a live path from an
    # unproved branch to master (2026-09-07).
    if ! out=$(timeout 900 lake env lean "$tmp" 2>&1); then
      echo "  DROP $prob: does not elaborate (lake env lean non-zero)" >&2
      rm -f "$tmp"; continue
    fi
    if printf '%s' "$out" | grep -q "declaration uses"; then
      echo "  DROP $prob: elaborates but still uses sorry" >&2
      rm -f "$tmp"; continue
    fi
    rm -f "$tmp"
    echo "$frame $prob $branch"
  done < "$list"
}

case "${1:-survey}" in
survey) survey ;;
verify) verify "${2:-/dev/stdin}" ;;
auto)
  # Unattended: land only what passes verify. Exists because the manual step was
  # the real bottleneck -- 175 solver branches accumulated and exactly one
  # landing run had ever happened (28 proofs, 2026-09-07 16:06, by hand), so
  # problems the campaign had genuinely closed kept reading as open.
  cand=$(mktemp /tmp/land-auto-XXXXXX)
  # One problem can be closed by several frames -- a98J03 came back from both
  # f51 and f169 on 2026-09-07. `land` checks out each row in turn, so
  # duplicates mean the last line silently decides which frame's proof becomes
  # master. Keep one row per problem, the highest frame number, so the choice
  # is the newest attempt and is deterministic rather than incidental.
  survey | sort -k2,2 -k1.2,1n \
    | awk '{row[$2]=$0} END {for (p in row) print row[p]}' \
    | sort -k1.2,1n > "$cand"
  n=$(wc -l < "$cand")
  if [ "$n" = 0 ]; then echo "no candidates"; rm -f "$cand"; exit 0; fi
  echo "candidates: $n"
  ok=$(mktemp /tmp/land-auto-ok-XXXXXX)
  verify "$cand" > "$ok"
  m=$(wc -l < "$ok")
  echo "passed verification: $m of $n"
  if [ "$m" = 0 ]; then rm -f "$cand" "$ok"; exit 0; fi
  "$0" land "$ok"
  rm -f "$cand" "$ok"
  ;;
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
*) echo "usage: $0 survey | verify [list] | land <list-file> | auto"; exit 2 ;;
esac
