# make-blueprint.md: how to write an apm-lean blueprint

From claude-14, 2026-10-23. The packet you were sent gives the problem, the
worktree and the files you may touch. This file gives the procedure. It applies to a
new blueprint, a statement repair, a split of one LIBRARY lemma and a re-split.

Each check below comes from a review where a blueprint was sent back or
fixed after review. The problem names are there so you can look the cases up in
~/notes/packets/blueprints/QUEUE.md; you do not need to read them to follow the step.

The order matters. You write and check all the statements first, then compile them as
a skeleton where every leaf is `sorry`. You write proof text only for the assembly.
A false or empty leaf is cheap to fix while it is one line. Once a seat has spent a
job on it, it costs that job.

## Step 0. Read before you state anything

1. problems/P/problem.md is the authority. Main.lean is the registered Lean version;
   its theorem and everything it defines stay byte-identical. Add things, never change them.
2. Search for results that already exist before you write a leaf for them:
   `grep -rl` the key notion in ConstructionTargets/ and holes/labs/blueprints/*/,
   then check that the file you would use has no `sorry` in it. The manifold Sard
   theorem that a t96J05 leaf asked for was already proved in the library
   (T93A04ManifoldWork.null_critical). Wherever a sorry-free result fits, use it
   instead of a leaf.
3. For a split, read the lemma's ancestors in the blueprint (the lemmas it was split
   from), not only the lemma itself. You need them for check C9.

## Step 1. Triage the target statement

Try to break the statement before you plan a proof: empty set, zero space,
dimension 0, trivial group, a constant function, boundary points, sign
conventions, and any counterexample the solve loop recorded. Compare it with
problem.md sentence by sentence.
- If the statement is true and faithful to problem.md, go to Step 2.
- If it is false or does not say what problem.md says, write the repair:
  RevisedMain.lean with the smallest change that problem.md warrants, plus the
  counterexample in BLUEPRINT.md. Then do Step 2 against the revised statement. Never
  narrow a statement to make it easier. A narrower statement counts as a different
  problem (m99J06 was sent back for this).

## Step 2. Write the statement ladder (no proof text yet)

Write the assembly top-down. Start from the main theorem and write the steps of its
proof as the statements of separate lemmas. Then repeat for any statement that is
still too large. Stop when each leaf is one seat's job: 30-150 lines of proof, at the
layer where Mathlib has the tool. Name that tool in BLUEPRINT.md and `#check` it.

Form rules:
- Every leaf is a top-level `theorem` whose whole body is `sorry`. No `def`,
  `structure` field or instance may contain `sorry`, or use a leaf. If a def's body
  uses a sorry'd lemma, every leaf about that def carries sorryAx, and the checker
  rejects them all even when they are proved (t02A01). Prove such membership facts
  inline in the def.
- Each leaf can be stated on its own, given the definitions block. It never mentions
  a local `have` or another lemma's hypothesis.
- Parallel by construction: if leaf B needs leaf A's conclusion, B takes that
  conclusion as an explicit hypothesis. The checker rejects a leaf whose axioms include
  another leaf's sorry.
- Split by shared dependency, not by conclusion. If two leaves would both have
  to prove the same technical fact, state that fact as its own leaf.
- Witnesses are passed in, not existentially re-obtained. If a leaf works with a cover,
  chart or iso that some other lemma produces, it takes that object as parameters with
  the properties it needs. Do not destructure an opaque `∃` from a sibling
  (t00A01 `_aux_mid_connecting`).
- Coordinates are canonical. If several leaves state equations "in coordinates", the
  coordinate isos are defs built from the parameters. Do not write `∃ e, …` in one leaf
  and take `(e : …)` arbitrary in another. Sign flips of an arbitrary iso are the
  usual counterexample (t99A01, three times in one problem).
- Universes are tied. `∃ E : Type*` inside a statement brings in a free universe. A
  wrong statement can then compile because the free universe accepts anything. Use
  `E : Type u` for `X : Type u`. If you need smallness, state it with `Small.{v}`
  and `Shrink` (CoveringSubgroupCorrespondence).
- No placeholder leaves. Never state `True`, or anything trivially provable, to mark a
  step.
- Do not import SphereCap* or LinearGraphMeasure (they install a second
  MeasurableSpace on EuclideanSpace).

## Step 3. Check every leaf against the review list

For each leaf, go through C1-C10. Record in BLUEPRINT.md, per leaf, which ones you
checked and how. If you cannot convince yourself that a leaf is true, say so in plain
words and keep it out of the queue.

- **C1 True as stated, at the stated generality.** Most review rejections were
  leaves that are true for the intended object and false in the stated generality.
  Build a counterexample in the most general setting the statement allows:
  - a gluing step stated over an arbitrary T2 space failed on the open tripod
    (t00A04 F2), and needed the hypothesis that local homology has a single nonzero
    element;
  - a leaf stated for an arbitrary family `C : Fin 4 → …` failed when `C 2 = C 3`
    (WedgePermutationCover);
  - a missing margin made a97J08 G1 false;
  - t02A03 L6b claimed `ContinuousAt r q0` in all of ℝ³ for a retraction built from a
    ratio `λ = dArc/(dArc + dD)` that is `0/0` at `q0`. Off the box (`v > 1`) the
    denominator can be smaller than the numerator, so `λ` is unbounded near `q0` and
    `(r q).1` does not tend to 0 along `(θ, 0, 1 + θ)`. Within the box `λ ∈ [0,1]`
    and the claim holds. State continuity at a singular point as
    `ContinuousWithinAt f domain x`, which is all a pasting argument uses.
  If the leaf needs a property of the intended object, add it as a hypothesis and
  make that property its own leaf.
- **C2 Not vacuous.** No hypothesis restates the conclusion, and no predicate used as
  a hypothesis is defined as the conclusion (a97J08 v2: `IsOrientedGridBoundary :=
  Σ winding = 1`). Data that stands for a computed quantity is computed, not passed in
  as a parameter.
- **C3 Not overloaded.** No leaf carries the whole argument. Ask what a seat
  holding only this leaf must prove. If the answer is "the theorem", the split
  has failed. Examples: a97J08 G2 carried the Jordan argument; a universe bridge
  restated all of F at universe u with no hypothesis supplying the Type-0 result
  (t00A04).
- **C4 The induction or assembly closes from its hypotheses.** For each assembly
  step, check that the hypotheses cover every case the step meets. t00A04 F3 was
  "finite induction over charts". Its intersections were compact but not
  convex, so no hypothesis applied to them, and Hatcher's step 3 was hidden there.
- **C5 Interfaces carry the maps the consumer uses.** If a structure packages
  equivalences (U ≃ₕ P, U ∩ V ≃ₕ S), check that the consumer's hypotheses about
  specific maps can reach them. CCSH's HasStandardCover first gave the equivalences
  with no link to `boundaryMap`, so the `boundaryHomologyMap = 0` hypotheses could not
  be used. Add the compatibility (the inclusions transported along the equivalences
  are homotopic to the named maps).
- **C6 Faithful hypotheses.** Nothing problem.md states is dropped or weakened, and
  nothing it does not state is added. Watch definitions that quietly drop a
  condition: `IsMinOn` carries no membership (m95A03).
- **C7 Lean semantics.** `(⊤ : WithTop ℕ∞)` is analytic (ω), not smooth. Natural
  subtraction, `x / 0 = 0` and `Real.sqrt` of a negative all change statements without
  any error. Check the smoothness orders and casts you write.
- **C8 Degenerate cases.** Check the empty set, dimension 0, n = 0 in an induction
  (S⁰, S¹ at the base), boundary points and the trivial group. Write in BLUEPRINT.md
  which ones you checked.
- **C9 Not a repeat (splits).** Compare each new leaf with every ancestor's
  statement. On t00A01 a split produced a leaf identical to an ancestor three levels up,
  and a seat spent a job proving the converse.
- **C10 Prose matches the file.** BLUEPRINT.md describes the Lean you are handing in.
  Delete or rewrite any paragraph from an earlier revision that no longer holds. The
  "Missing subprogram" text in t00A04 and the stale "Sard open" note in t96J05 both
  misled the reader.

## Step 4. Compile the skeleton

Compile only through the lock and the memory scope your packet gives. Test the
error count; do not pipe compile output into `head`:

    out=$(mktemp); flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q \
      -p MemoryMax=12G lake env lean holes/labs/blueprints/P/Blueprint.lean >"$out" 2>&1
    grep -c ': error' "$out"      # must print 0

Lean turns a declaration that fails to elaborate into sorryAx. So "only sorry
warnings" is not enough: check that there are 0 errors, and that the sorry warnings
are exactly your leaves (count them). Then `#print axioms` the main theorem. It
must show standard axioms plus sorryAx, and the sorryAx must come only through the
leaves. Run `python3 scripts/statement-registry.py check P` and confirm it matches.

## Step 5. Size and order

For each leaf, record: its name, one line in words, the proof sketch with the Mathlib
or ConstructionTargets results to use, a size estimate, what it depends on, and
whether it is LIBRARY. Then list the dependency layers. A leaf estimated over
about 200 lines is LIBRARY. Split it again now, or mark it LIBRARY and say what
foundation is missing, rather than hiding it inside a leaf of ordinary size. Order
the queue easiest first.

## Step 6. Reply

Bell the sender back (the packet names them). Send: the triage verdict, the leaf table
from Step 5, the C1-C10 record per leaf (one line each is enough, e.g.
"C1 tripod-style test: needs hloc, added; C8 d=0 ok"), the error count, the
sorry-warning count, the `#print axioms` output, the registry result, and what you
doubt. Commit only if the packet says so.
