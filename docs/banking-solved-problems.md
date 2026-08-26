# Banking solved problems

Date: 2026-08-26
Status: describes existing practice, written down after the fact

## What banking is, and why it is not optional

A frame's proof work happens on a throwaway git worktree under
`~/code/apm-frames/<frame>-<problem>-solver`, on a branch
`exp/countdown-<frame>-<problem>-solver`. When the frame closes, **the worktree
is retired and removed**. What survives is the branch — and, in practice,
nothing else points at it.

That is the whole reason this procedure exists. On 2026-08-26 four solved
problems (a95J04, a97J05, a97J06, a97J07, from frames f35/f40/f41/f42) were
each reachable from **exactly one ref**, their own `exp/countdown-*` branch,
with the worktrees that produced them already gone. A prune of `exp/` refs, or
any cleanup that treats those branches as spent scratch, would have destroyed
four completed proofs — while the campaign records went on citing them as
solved with terminal heads that no longer resolved.

Banking replays the solved file onto a `bank/` branch that is merged to
`master`, so the proof lives on the trunk that actually gets backed up.

## Naming

    bank/<first-frame>-<last-frame>-<YYYYMMDD>

e.g. `bank/f22-f25-20260823`, `bank/f35-f42-20260826`. Frames named are the
ones banked in that batch, not a contiguous range — f35-f42-20260826 banks
f35, f40, f41 and f42, because f34 and f37 were already on master.

Exceptional one-offs use a descriptive suffix instead of a range:
`bank/t01A03-exceptional`.

## Procedure

Branch from `master`, never from a frame branch.

**Per solved problem, two commits.**

1. **The solve.** One commit touching exactly one file,
   `problems/<pid>/lean/Main.lean`, whose content is byte-identical to the
   frame's terminal head. Reuse the original solve commit's subject line
   verbatim ("Solve a97J07 by maximum modulus"), so the bank reads as the work
   it records rather than as bookkeeping. Note the source head in the body.

2. **The metadata.** One commit touching exactly one file,
   `problems/<pid>/status.json`, subject
   `Recompute <pid> metadata after banking the <frame> solve`. In it:

   - `lean.sorry_count_main` and `lean.sorry_count_total` → `0`
   - `classification` → `"solved"`
   - **delete** `checked_at` and `checked_lean_state` — they describe a
     pre-solve elaboration and are now false
   - add `boundary`: prose saying which frame and campaign closed it, the
     source head it was banked from, and that the frozen statement is unchanged
   - add `sorry_audit`: `method`, `at`, `elaborated_exit`, `sorry_declarations`,
     `previous_classification`, `previous_sorry_count_total`, `axioms`, `frame`

Keep the two kinds of commit separate. A reader bisecting for "when did this
problem become solved" wants the Lean change alone.

## Verification, before committing anything

Each of these has been got wrong at least once; run all of them.

**Is it actually unbanked?** Compare *content*, not commit reachability.
Banking re-applies the file as a new commit, so the original head is never an
ancestor of `master` and `git branch --contains` will always say "unbanked":

    git show <head>:problems/<pid>/lean/Main.lean   | sha256sum
    git show master:problems/<pid>/lean/Main.lean   | sha256sum

Equal digests mean it is already banked, whatever the graph says. This is how
f34 and f37 were nearly banked a second time.

**Is it actually solved?** `grep -c sorry` counts the word in comments and
lies. a97J06 shows three hits, all of them prose discussing a sibling problem.
Strip comments, or better, elaborate and read the warnings:

    lake env lean problems/<pid>/lean/Main.lean

Zero `declaration uses 'sorry'` warnings and exit 0 is the artifact. Then check
the axioms, which is the check that cannot be talked around:

    #print axioms apm_<pid lowercased>

`[propext, Classical.choice, Quot.sound]` is clean. **`sorryAx` anywhere in
that list means it is not solved**, whatever the file looks like and whatever
the frame receipt says.

**Did you compile Mathlib by accident?** You should not have. Mathlib is
prebuilt under `.lake/packages/mathlib/.lake/build/lib/lean/`; single-file
elaboration against it takes 3-5 seconds. The project's own
`.lake/build/lib/Mathlib.olean` must still be **absent** afterwards. If it
appeared, a build compiled Mathlib and the machine was loaded for an hour.

**Do the shas you wrote down resolve?** `git cat-file -e <sha>` on every sha
that ends up in a `boundary` field. An abbreviated sha copied out of terminal
output and then padded to full length is a fabrication that looks exactly like
a real one.

## Working safely in a shared checkout

`~/code/apm-lean` usually has a branch checked out that belongs to someone
else's in-flight work, and carries many live worktrees. **Do not switch its
branch.** Build the bank in its own worktree:

    git worktree add -b bank/<name> /tmp/apm-bank master

Elaboration still runs from the main checkout, which is where `.lake` lives,
pointed at the worktree's file — this needs no mutation of the main checkout:

    cd ~/code/apm-lean && lake env lean /tmp/apm-bank/problems/<pid>/lean/Main.lean

Remove the worktree when the branch is merged.

## The standing problem this does not solve

Banking is manual, retrospective, and unprompted: it happens when someone
notices. Between f34 (banked 2026-08-25) and this batch, four solved problems
sat on single unreferenced branches for up to eleven days. Nothing in the frame
machine emits a bank, nothing alarms when a solved problem is unbanked, and the
`:problem/outcome :solved` terminal receipt does not check that the head it
names is reachable from anything durable.

The obvious closure is to make it part of the loop: on a terminal receipt with
`:problem/outcome :solved`, verify the head elaborates with no `sorryAx`, then
bank it and recompute metadata as two commits. Frame close is exactly when the
information needed is all in hand and the worktree still exists. Until that is
built, `bank/` batches will keep being written by whoever notices, and the
window between solving and banking is a window in which a routine branch
cleanup loses proofs.
