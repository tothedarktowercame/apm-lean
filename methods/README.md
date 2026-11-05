# Methods

How the proofs in this repository were made: written so that someone else,
with their own agents, could run the same process. The process changed over
the campaign (March to November 2026), so this describes it as it stood at the
end, with pointers to the history where earlier choices still matter.

## The pipeline in one page

1. **Statement.** Each problem gets a Lean statement in
   `problems/P/lean/Main.lean`. An outside grader, an agent that did not write
   the statement and only reads, compares it with the problem text. If the grade
   is acceptable, the statement's fingerprint goes into the registry
   (`problems/STATEMENTS.json`). From then on, nobody may change the statement
   while proving it. [01-statements.md](01-statements.md)
2. **Direct attempt.** A solve loop gives the problem to one agent with a
   time budget. Most problems were closed by this loop or by earlier versions
   of it.
3. **Blueprint.** For a problem that resists, an agent writes a blueprint: the
   main theorem proved from named lemmas ("leaves"), each with body `sorry`,
   each checked against a list of ways a leaf goes wrong before any proof work
   starts. [02-blueprints.md](02-blueprints.md)
4. **Lemma seats.** Each leaf goes to its own agent session (a "seat"),
   in parallel. A seat edits only its leaf's area of a copy of the blueprint.
   A mechanical checker compares the result with the template and accepts it
   only if it compiles and the leaf's axioms are clean. Accepted proofs are
   spliced into the blueprint. A partial result is split into smaller leaves and
   queued again. [03-lemma-seats.md](03-lemma-seats.md)
5. **Library.** A leaf that would take more than about 200 lines, or that
   several problems need, is library work. It is split the same way, but lives
   in `ConstructionTargets/`, where other problems can import it.
   [04-library.md](04-library.md)
6. **Landing.** When the blueprint has no `sorry`, it is copied over
   `Main.lean`. A script checks the registry fingerprint, compiles the file,
   checks `#print axioms`, updates `status.json`, commits and merges.

The checks in steps 1, 4 and 6 are scripts, not judgement. The judgement goes
into steps 1 (grading), 3 (is each leaf true, and does it say something?) and
the review of partial results in step 4.

## What you need to reproduce it

- Lean `v4.29.0-rc8` and the Mathlib revision pinned in `lake-manifest.json`.
- Agents that can edit a file, run `lake env lean`, and report back. The
  instructions they were given are in [`tools/`](tools/), verbatim. Nothing in
  them depends on a particular model.
- A way to send an agent a job and get its reply. We used a local
  coordination server (futon3c "Agency"), which is not part of this
  repository. The dispatch scripts call it through `agency_send.py`. Any job
  queue that can start an agent with a prompt and collect its final message
  will do; [tools/README.md](tools/README.md) lists which lines to replace.
- Enough memory for parallel Lean compiles. Each compile ran in a
  `systemd-run --scope -p MemoryMax=12G` cgroup, behind one `flock`, so that
  eight seats did not run eight Mathlib-sized elaborations at once.

## Numbers

From 2026-10-13 to 2026-11-05 the lemma rounds landed 2040 leaf proofs and
closed 95 problems that the solve loop had not closed. These counts come from
our progress log, which is not in this repository. The closed/open counts in
the top-level README can be recomputed from `problems/*/status.json`.

## Lessons that changed the process

Each of these is written into the procedure where it applies. They are
collected here because they are the parts most likely to transfer.

- **Statements drift unless frozen.** On 2026-09-28 an audit found that 18 of
  62 closed topology problems were narrower than the problem, vacuous, or
  assumed the core of what they were meant to prove. The registry exists
  because of that audit.
- **Check leaves before proving them.** Most rejected blueprints had a leaf
  that was true for the object the author had in mind and false at the
  generality it was stated in. Finding that costs one line of thought before
  dispatch and a whole seat's job after it.
- **A partial result must bank work.** A seat that runs out of time leaves
  proved helpers and smaller, true `sorry` leaves for the next seats. A
  commented-out attempt is worth nothing.
- **Seats claim compiles they did not see.** The checker compiles every
  returned file itself. A seat's "it compiles" is not evidence.
- **No `sorry` inside a definition.** Every theorem about such a definition
  inherits `sorryAx`, so a correct proof of it still fails the axiom check.
