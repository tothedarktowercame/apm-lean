# 3. Lemma seats: parallel proof of blueprint leaves

Once a blueprint compiles and its leaves have passed review, each leaf is
proved by its own agent session, a **seat**. Many seats work on the same
problem at once. This works because the leaves were stated to be independent
(see [02-blueprints.md](02-blueprints.md)). It is safe because a
mechanical checker, not the seat, decides whether a proof is accepted.

The scripts and agent instructions described here are in [`tools/`](tools/),
exactly as they were run.

## Layout

All lemma work happens on one branch (`lemmas`) in one worktree, separate from
`master`:

    holes/labs/blueprints/P/Blueprint.lean   the blueprint (leaves = sorry)
    holes/labs/lemmas/P/NAME.lean            seat file for leaf NAME of problem P

A seat file is the whole blueprint, with leaf `NAME` wrapped in two marker lines:

    -- BEGIN SEAT AREA
    theorem NAME ... := by
      sorry
    -- END SEAT AREA

For a shared library module, `P` is written `CT.Module`, and the template is
`ConstructionTargets/Module.lean`. See [04-library.md](04-library.md).

## One leaf, start to finish

1. **Make the file.** `lemmatool.py make P NAME` copies the current blueprint
   and wraps the leaf in the seat markers. The file is committed, so that
   the commit can serve as the template later.
2. **Dispatch.** `next.sh SEAT` takes the next `P NAME` line from the queue,
   makes the file, and sends the seat a job. The job text is
   [`tools/preamble.md`](tools/preamble.md) followed by a line naming
   the problem, the leaf and the files to read. Each job starts a fresh agent
   session; a long-lived session overflows its context window.
3. **The seat works.** It may edit only between the markers. It replaces the
   leaf's `sorry` with a proof, and may add helper lemmas named `NAME_aux_*`
   above the leaf. It compiles with
   `flock <lock> systemd-run --user --scope -p MemoryMax=12G lake env lean <file>`
   as often as it likes. It does not commit. It replies with one of the
   following:
   - **PROVED**, with the line count;
   - **PARTIAL**, with the exact remaining goal;
   - **BLOCKED-ON X**, if the leaf cannot reasonably be proved without leaf X,
     which is still open.
4. **Check.** `lemmatool.py check P NAME` accepts the file only if:
   - the text outside the seat area is byte-identical to the template (the
     commit that made the file, so leaves spliced since then do not count as
     edits);
   - the leaf's statement (everything before `:= by`) is unchanged;
   - the area contains no `sorry`, `admit` or `axiom`;
   - the file compiles with 0 errors;
   - `#print axioms NAME` shows no `sorryAx`. This also catches a proof that
     relies on another leaf that is still open.
5. **Splice.** `lemmatool.py splice P NAME` copies the seat area into the
   blueprint. Helpers the blueprint already contains are dropped.
6. **Land the problem.** When the blueprint has no `sorry` left,
   `land_problem.sh P` does the following:
   - copies it over `problems/P/lean/Main.lean`;
   - re-checks the registry fingerprint, recompiles, and runs
     `#print axioms` on the registered theorems, refusing on `sorryAx` or a
     `native_decide` axiom;
   - sets `sorry_count_main` to 0 in `status.json` and commits;
   - calls `merge_lemmas.sh`.
7. **Merge.** `merge_lemmas.sh` merges `lemmas` into `master` on a scratch
   worktree. It stops for a person on any of these: a path outside
   `problems/` and `holes/labs/`, a changed lakefile or manifest, or a registry
   mismatch. It builds the changed library modules, if any. Only then does it
   fast-forward `master` and push.

Only the seat's own message is ever taken on trust, and only as a hint about
what to check. On 2026-10-25 a seat reported PROVED from two compile calls that
had been cut off after 34 seconds. Its file had 9 errors. The checker caught it.

## Partial results

In the round log, 1832 seat results were checked and spliced, and 248 came
back PARTIAL. Seven leaves turned out to be false as stated and went back to the
blueprint author. The rules for a partial decide whether the next round gains
anything:

- the leaf itself must be written as an assembly of `NAME_aux_*` helpers, so
  that the only `sorry`s left are in helpers. That shows the helpers suffice;
- each finished step is a proved helper, and each unfinished step is a
  separate `sorry` helper with a true, precise statement;
- every helper must be used by the assembly;
- the partial must compile, and the seat must have seen it compile;
- a `sorry` followed by a commented-out attempt counts for nothing.

The reviewer (the agent running the round) checks each new `sorry` helper
against the blueprint checks, C1 in particular. It rejects restatements: a
helper whose conclusion is the target's, renamed, or an existential that a
trivial witness satisfies exactly when the target holds. It splices the proved
helpers and queues the remaining ones as new leaves. In this way a leaf of 300
to 600 lines became a dozen seat-sized leaves.

Later rounds used a second style for leaves that needed more room. The seat got
a full copy of the blueprint, with the instructions in
[`tools/prove-preamble.md`](tools/prove-preamble.md). The reviewer then
merged the seat's file back against the base revision with `git merge-file`.
[`tools/dispatch-tmpl.sh`](tools/dispatch-tmpl.sh) is the template for those
rounds.

## Blocking and ordering

The queue is a text file of `P NAME` lines, easiest first. A leaf that comes
back BLOCKED-ON X goes back on the queue, and is sent again after X lands.
`next.sh` and the landing script hold the same lock, so a seat file is never
made from a blueprint that has been spliced but not yet committed. `next.sh`
also refuses to regenerate a seat file that has uncommitted edits, because that
file may hold a proof that has not landed yet.

When seats are scarce, take the leaves on the critical path first: the leaves
that gate the most remaining work in the problems closest to closing.

## Seats and costs

Seats were mostly OpenAI Codex sessions. When Codex quota ran out, Moonshot Kimi
and Zhipu GLM sessions were used, and their results went through the same
checker. Up to eight seats ran at once. The limit was disk and memory load from
concurrent Lean compiles (2-5 minutes each against Mathlib), not the agents.
All compiles went through one `flock`, and each ran in a 12 GB memory cgroup.

Two operational rules kept seats from hurting each other on a shared machine:

- search only inside the worktree (`rg PATTERN ConstructionTargets
  .lake/packages/mathlib/Mathlib`). Two seats once ran `rg` over the whole home
  directory for an hour.
- never `lake build` and never update packages. `.lake/packages` is shared.
