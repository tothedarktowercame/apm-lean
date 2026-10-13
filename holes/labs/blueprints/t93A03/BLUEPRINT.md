# Blueprint for t93A03

## Triage and repair

Verdict on `problems/t93A03/lean/Main.lean`: **unfaithful (vacuous)**.

The source asks only to prove that
`(S¹ × S²) # (S¹ × S²)` is not simply connected.  The old Lean statement
instead assumes

```text
T93A03ConnectedSum φ₁ φ₂ ≃ₕ T93A03Spine
```

where `T93A03Spine` is a wedge of two circles.  This is false: the left side
is a closed orientable three-manifold with nonzero `H₂` (indeed `ℤ²`) and
`H₃` (`ℤ`), whereas a wedge of circles has zero homology in those degrees.
Consequently the hypothesis has no inhabitants for the intended connected
sum.  Moreover, the old proof obtains non-simple-connectivity directly by
transport across this false equivalence, so the hypothesis carries the core
of the requested proof.  This is exactly the counterexample recorded by
`holes/labs/statement-registry/triage-2.md`.

`RevisedMain.lean` removes both the false `hspine` hypothesis and the unrelated
extra conclusion computing the fundamental group of the auxiliary spine.  Its
conclusion is exactly the sentence in `problem.md`.  It retains the concrete
quotient construction and adds radius-two extensions of the embedded
radius-one balls.  These are exterior collars: they express the tame standard
balls implicit in the notation `#` and exclude wild embeddings for which the
quotient need not have the standard connected-sum open-cover geometry.  This
is the same collar interface already used by the reviewed `t98A02` connected-
sum blueprint.  It is geometric input, not a hypothesis containing the desired
fundamental-group conclusion.

There is no short compiled `Refute.lean`: formalizing the homology mismatch is
itself one of the large topology-library gaps.  The mathematical refutation is
the `H₂/H₃` calculation above.

Degenerate checks: the closed three-ball is nonempty, and an embedding into
`Circle × S²` rules out an empty summand.  The collar extension implies the
boundary sphere has a genuine exterior neighborhood, so the wild-ball failure
mode is unavailable.  For the standard product-chart balls the repaired
quotient is the usual connected sum, whose fundamental group is
`ℤ * ℤ = F₂`.  The registry counterexample no longer applies because no
homotopy equivalence with a one-dimensional wedge is asserted.

## Definitions

The Euclidean ball, sphere, summand, punctured summand, gluing relation,
quotient, and quotient topology are copied from `Main.lean`.  The only new
definitions are `T93A03CollarBall` (the radius-two ball) and
`t93A03DiskInCollarBall` (the literal radius-one inclusion).  No definition
packages a fundamental-group or non-simple-connectivity conclusion.

The blueprint imports the sorry-free
`ConstructionTargets.PointWedgeVanKampen` foundation.  That module supplies
the generic point-wedge van Kampen infrastructure already built by the
topology program; it does not yet supply the connected-sum collar comparison
needed here.

## Lemmas

### `t93A03_collaredConnectedSum_piOne` — LIBRARY

**Statement.** Given two embedded three-balls in `S¹ × S²`, each extending to
an embedded radius-two ball, the concrete glued quotient has a basepoint at
which its fundamental group is multiplicatively equivalent to
`FreeGroup (Fin 2)`.

**Why true.** Use each radius-two extension to construct an open collar cover
of the quotient.  The left and right pieces deformation-retract to the two
punctured summands and their intersection retracts to `S²`.  Removing the
collared ball does not change `π₁(S¹ × S²)`, and the product projection plus
the simple connectivity of `S²` computes each piece's group as `ℤ`.  The
intersection is simply connected.  Van Kampen therefore gives the free
product `ℤ * ℤ`, identified with `FreeGroup (Fin 2)`.

The closest sorry-free foundation is
`ConstructionTargets.PointWedgeVanKampen`: it contains the generic two-open
fundamental-groupoid/free-product machinery and the circle-coordinate work.
What is missing is the collared connected-sum open cover, its three deformation
equivalences, and the punctured-`S¹ × S²` comparison.  This is a genuine
300+ line library program (the fundamental-group analogue of
`program-2026-10-13-collared-connected-sum-homology`), so it is stated once
rather than split into adapters that would conceal their shared geometric
dependency.

**Estimate.** 600–1,200 lines across a reusable collared connected-sum module;
under 100 lines for this specialization after that module exists.

**Dependencies.** None among the blueprint lemmas.  External dependency:
`ConstructionTargets.PointWedgeVanKampen` plus the missing collared connected-
sum comparison program.

**Truth check.** For standard coordinate balls, the hand van Kampen
calculation is `π₁ = ℤ *_{1} ℤ = F₂`.  The overlap contributes no relation
because `π₁(S²) = 1`.  A single summand already contributes a nontrivial
generator, and the two inclusions give the two distinct free generators.  The
collar hypotheses explicitly eliminate the only geometric degeneracy found in
triage (wild embedded balls without usable exterior neighborhoods).

### `t93A03_not_simplyConnected_of_piOne_equiv` — proved

**Statement.** If `π₁(X,x)` is equivalent to `FreeGroup (Fin 2)`, then `X` is
not simply connected.

**Why true.** Under a `SimplyConnectedSpace X` instance, Mathlib makes the
loop quotient at `x` a subsingleton.  Transporting equality of the preimages
of `FreeGroup.of 0` and `1` through the equivalence contradicts
`FreeGroup.of_ne_one`.

**Estimate.** 10–20 lines; already compiled without `sorry`.

**Dependencies.** None.  It accepts the library lemma's group equivalence as
an explicit parameter, so it was checked independently.

**Truth check.** `Fin 2` is nonempty (`0 : Fin 2`), and
`FreeGroup.of_ne_one 0` verifies that the selected generator is not the
identity.  Thus there is no empty-generator edge case.

## Dependency layers

- Layer 1, parallel: the LIBRARY program
  `t93A03_collaredConnectedSum_piOne`; the already completed generic
  obstruction lemma `t93A03_not_simplyConnected_of_piOne_equiv`.
- Layer 2, already compiled: `apm_t93a03` extracts the equivalence from Layer
  1 and applies the Layer-1 obstruction lemma.

There are two top-level blueprint lemmas: one LIBRARY lemma with `sorry` and
one fully proved lemma.  The repaired main theorem contains no `sorry`.  I am
convinced both statements are true; the uncertainty is implementation size of
the reusable collar/open-cover comparison, not mathematical validity.

## Compile and axiom gate

Commands:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t93A03/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t93A03/Blueprint.lean
```

Both exit successfully.  Output of `#print axioms apm_t93a03`:

```text
'apm_t93a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` enters only through `t93A03_collaredConnectedSum_piOne`.
