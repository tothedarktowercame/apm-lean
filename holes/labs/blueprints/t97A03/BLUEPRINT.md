# Blueprint for t97A03

## Triage

Verdict: **true and faithful**.

The source asks for the possible connected two-fold covers of the space formed
by identifying two distinct points of a circle with the north and south poles
of a two-sphere, and for their homology and fundamental groups.  The Lean
statement uses the corresponding literal `EqvGen` quotients, asserts that the
total space is homeomorphic to one of the two possible pictures, and gives the
expected integral singular homology and based fundamental group.  The
registered statement was also reported as graded faithful by the batch owner.

I tried the relevant degeneracies.  The hypothesis `A ≠ B` excludes collapse
of both sphere poles onto one circle point.  The fiber-cardinality equation
excludes the empty total space and, as the proved
`apm_t97A03_surjective_of_fiber_card_two` shows, forces surjectivity.  For each
base point, `apm_t97A03_fiber_equiv_fin_two` upgrades the numerical condition
to an actual two-element fiber.  Connectedness excludes the trivial disjoint
union of two copies of the base.  No solve-loop counterexample or repair was
recorded.

The hand check is the standard CW calculation.  The base has two vertices,
three edges, and one two-cell with zero cellular boundary, hence homotopy type
`S² ∨ S¹ ∨ S¹`.  A connected double cover is determined by a nonzero map
`F₂ → Z/2`; its three choices give two homeomorphism types.  Every cover has
four vertices, six edges, and two two-cells with zero boundary.  Thus
`H₀ = Z`, `H₁ = Z³`, `H₂ = Z²`, and higher homology vanishes.  Its fundamental
group has rank `1 + 2(2 - 1) = 3` by Nielsen--Schreier.

## Reused compiled work and imports

The quotient definitions, both generating attachment equalities,
`apm_t97A03_surjective_of_fiber_card_two`, and
`apm_t97A03_fiber_equiv_fin_two` are copied from the best compiled solve-loop
state and retain their proofs.

The blueprint imports these sorry-free foundations so lemma seats do not need
to change imports:

* `ConstructionTargets.SuppliedCoverAlgebra`, providing the equivalence from
  the total-space fundamental group to the range of the induced map;
* `ConstructionTargets.FiniteIndexFreeGroupSchreierRank`, including the
  index-two subgroup of `FreeGroup (Fin 2)` calculation;
* `ConstructionTargets.PointWedgeVanKampen`, the completed point-wedge van
  Kampen foundation;
* `ConstructionTargets.ProductionOpenCoverMayerVietoris`,
  `ConstructionTargets.SphereHomology`, and
  `ConstructionTargets.CircleSingularHomology` for the model calculation.

The topology worklist records the first two algebra adapters as banked in
`SuppliedCoverAlgebra`.  It also records that the old general
covering-subgroup construction was superseded: this problem needs analysis of
the supplied cover, not construction of a cover from an arbitrary subgroup.

## Remaining lemmas

### `apm_t97A03_classify_connected_double_cover` — LIBRARY

**Statement in words.** Every connected covering of the literal base whose
fibers all have cardinality two is homeomorphic to either the one-lifted-circle
model or the two-lifted-circles model.

**Why true.** Split the inverse image of the simply connected sphere into its
two sheets.  Label the sheets over one pole, lift the two complementary arcs
of the attached circle, and record whether each arc preserves or swaps the
sheet label.  Connectedness says that the resulting pair of bits is not
simultaneously trivial.  The patterns `(1,0)` and `(0,1)` are interchanged by
swapping the two circle arcs and produce the one-circle model; `(1,1)` produces
the two-circle model.  Descend the piecewise maps through the `EqvGen`
quotients and prove that the resulting bijective local homeomorphism is a
homeomorphism.

The closest completed inputs are the path-lifting and induced-fundamental-group
results behind `ConstructionTargets.SuppliedCoverAlgebra`.  What is still
missing is the global, explicit monodromy-to-quotient homeomorphism.  The
topology audit estimates this at 800–1600 lines, so it is intentionally one
library program rather than fake small lemmas.

**Expected size.** 800–1600 lines (LIBRARY).

**Dependencies.** Definitions and the two proved fiber lemmas only.  It does
not depend on the invariant lemma.

**Truth check.** Enumerating the nonzero elements of `(Fin 2 → Z/2)` gives
exactly three connected monodromies.  Swapping the two circle arcs identifies
the first two geometrically, leaving exactly the two quotient models in the
conclusion.  The discarded zero monodromy gives a disconnected cover, in
agreement with the `ConnectedSpace Y` hypothesis.

### `apm_t97A03_invariants_of_model` — LIBRARY

**Statement in words.** Any pointed space homeomorphic to either literal cover
model has integral singular homology of ranks `1,3,2` in degrees `0,1,2`, zero
homology above degree two, and fundamental group `FreeGroup (Fin 3)`.

**Why true.** For either model, choose quotient-compatible neighborhoods of
the two sphere sheets and lifted circle pieces.  Mayer--Vietoris reduces
singular homology to the cellular calculation with four vertices, six edges,
and two null-boundary two-cells.  Van Kampen (or a deformation to two spheres
wedge three circles) gives `F₃`; transport both results through the supplied
homeomorphism, including the basepoint change.  The imported sphere, circle,
Mayer--Vietoris, point-wedge, and finite-index Schreier modules provide the
large reusable ingredients.

The remaining missing work is the literal quotient/open-cover comparison for
these two models.  The topology audit estimates the complete packaged result
at 1500–3000 lines.  Keeping the model disjunction as a hypothesis makes this
program wholly independent of the classification program; it does not assume
the classification lemma's conclusion without receiving it as data.

**Expected size.** 1500–3000 lines (LIBRARY).

**Dependencies.** Definitions only, plus the imported sorry-free foundations.
It does not depend on `apm_t97A03_classify_connected_double_cover`.

**Truth check.** The lifted CW complex has Euler characteristic
`4 - 6 + 2 = 0`, equal to twice the base Euler characteristic.  Its connected
one-skeleton has cycle rank `6 - 4 + 1 = 3`; the two sphere cells have zero
boundary, giving two independent degree-two classes.  These checks yield
Betti numbers `(1,3,2)` and `π₁ = F₃` for both attachment patterns.  At an
arbitrary basepoint `y`, connectedness of either model supplies the usual
basepoint-change isomorphism, so the pointed conclusion is not restricted to
an attachment point.

## Assembly and dependency layers

The main theorem first applies the classification lemma, then passes its
result to the invariant lemma and assembles the conjunction.  Its proof has no
`sorry`.

* **Layer 1 (parallel library programs):**
  `apm_t97A03_classify_connected_double_cover` and
  `apm_t97A03_invariants_of_model`.
* **Layer 2 (already compiled):** `apm_t97a03` conjunction assembly.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97A03/Blueprint.lean
```

Lean reported exactly two `sorry` warnings, at the two LIBRARY lemmas.  The
final output of `#print axioms apm_t97a03` was:

```text
'apm_t97a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the registered theorem only through the two named
library obligations.
