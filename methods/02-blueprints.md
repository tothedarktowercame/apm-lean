# 2. Blueprints

A blueprint turns one hard problem into many small, independent Lean jobs.
It lives in `holes/labs/blueprints/P/`:

- `Blueprint.lean`: a copy of `Main.lean` with the main theorem proved
  from a set of named lemmas, the **leaves**. Each leaf is a top-level
  `theorem` whose whole body is `sorry`. The file compiles.
- `BLUEPRINT.md`: the triage verdict on the statement, then one entry per leaf:
  what it says in words, a proof sketch naming the Mathlib or library results to
  use, a size estimate, its dependencies, and which of the checks below were
  done and how.
- `RevisedMain.lean`, only when the registered statement had to be repaired (see
  [01-statements.md](01-statements.md)).

Blueprints were written by agents (Codex or Claude) from a packet naming the
problem, then reviewed before any leaf was dispatched. The full procedure
the authors followed is [`tools/make-blueprint.md`](tools/make-blueprint.md).
This page summarises it.

## Order of work

Write and check all the statements first. Then compile them as a skeleton in
which every leaf is `sorry`. Only then write proof text, and only for the
assembly that derives the main theorem from the leaves. A false or empty leaf
costs one line to fix while it is a statement. Once a seat has spent a job on
it, it has cost that job.

1. **Read.** Re-read `problem.md`. Search `ConstructionTargets/` and the other
   blueprints for results that already exist, and use sorry-free ones in place
   of leaves.
2. **Triage the target.** Try to break the main statement: empty set,
   dimension 0, trivial group, constant function, boundary points, sign
   conventions. If it is false or unfaithful, write the repair first.
3. **Write the statement ladder.** Write the proof top-down as a sequence of
   steps, and state each step as a separate lemma. Split again until each leaf
   is 30-150 lines of proof at a layer where Mathlib has the tool. Name that tool
   and `#check` it.
4. **Check every leaf** against C1-C10 below, and record the result.
5. **Compile the skeleton.** It must have 0 errors. The sorry warnings must be
   exactly the leaves; count them, because Lean turns a declaration that fails
   to elaborate into `sorryAx` without stopping. `#print axioms` on the main
   theorem must show `sorryAx` only through the leaves. The registry check
   must still pass.
6. **Size and order.** A leaf estimated at more than about 200 lines is
   library work: split it now, or mark it LIBRARY and say what foundation is
   missing. List the dependency layers and order the queue easiest first.

## Form rules for leaves

- The body of every leaf is exactly `sorry`. No `def`, structure field or instance
  may contain `sorry` or use a leaf.
- A leaf can be stated on its own, given the definitions. It never refers to
  a local `have` or another lemma's hypotheses.
- **Parallel by construction.** If leaf B needs leaf A's conclusion, B takes
  it as an explicit hypothesis. B can then be proved before A lands, and the
  checker can reject any leaf whose axioms include another leaf's `sorry`.
- **Split by shared dependency, not by conclusion.** If two leaves would both
  need the same technical fact, that fact is its own leaf; otherwise two seats
  prove it twice.
- **Witnesses are passed in.** A leaf that works with a cover, chart or
  isomorphism takes it as a parameter with the properties it needs, rather than
  unpacking an existential that a sibling leaf produces.
- **Coordinates are canonical.** If several leaves compute in coordinates, the
  coordinate maps are definitions built from the parameters. One leaf must not
  write `∃ e, …` while another takes an arbitrary `e`, because a sign flip of an
  arbitrary isomorphism is then a counterexample.
- **Universes are tied.** An `∃ E : Type*` brings in a free universe in which
  a wrong statement can still compile.
- **No placeholders.** A leaf never states `True` or anything else trivial.

## The review checks, C1-C10

These come from reviews in which a blueprint was sent back. The procedure
file gives the case that produced each check.

| | check | the usual failure |
|---|---|---|
| C1 | true as stated, at the stated generality | true for the intended object, false for an arbitrary one (a gluing step over any T2 space fails on the open tripod) |
| C2 | not vacuous | a hypothesis whose definition is the conclusion |
| C3 | not overloaded | one leaf that carries the whole argument |
| C4 | the assembly closes from its hypotheses | an induction step whose hypotheses do not cover the cases it meets |
| C5 | interfaces carry the maps the consumer uses | equivalences packaged with no link to the named maps |
| C6 | faithful hypotheses | a definition that quietly drops a condition (`IsMinOn` carries no membership) |
| C7 | Lean semantics | `⊤` smoothness, natural subtraction, division by zero |
| C8 | degenerate cases | empty set, dimension 0, base case of an induction |
| C9 | not a repeat | a split that reproduces an ancestor's statement |
| C10 | the prose matches the file | stale paragraphs from an earlier revision |

C1 caught the most. Before dispatching a leaf, try to build a
counterexample in the most general setting its statement allows. If the leaf
needs a property of the intended object, make that property a hypothesis, and
make proving it a separate leaf.

## Example

`t00J02` took the longest. The problem: f is a smooth self-map of a genus-2 surface,
transverse to a curve C around a handle, and every component of f⁻¹(C) bounds
an embedded disk; show that deg f = 0. Its blueprint went through
several re-splits. 60 seat files were proved against it. The final
`Blueprint.lean` is about 10,000 lines: the leaf proofs, together with the
library lemmas they needed, which were inlined. Its
`BLUEPRINT.md` and the git log for `holes/labs/blueprints/t00J02/` show each
split and why it was made.
