# Blueprint for t99A03

## Triage and repair

Verdict: **the registered theorem is true but unfaithful**.

`problem.md` asks two concrete questions: whether every self-map of the wedge
of four real projective planes has a fixed point, and the same question for
their fourfold connected sum.  The old `Main.lean` instead quantifies over
arbitrary spaces `E` and `B` and proves only that a nonidentity deck
transformation of a connected cover has no fixed point.  It mentions neither
requested space, entirely omits part (a), and does not construct the example
required in part (b).

This is not a false theorem, so there is no mathematical counterexample and no
`Refute.lean`: the defect is omission.  A concrete witness to the mismatch is
that the old theorem can be instantiated with any unrelated connected cover
(for example, the identity cover of a singleton has all the space/cover
hypotheses, although its `hne` premise is impossible).  Thus its conclusion
cannot distinguish either space in the source question.  This agrees with the
statement-registry grade `B` and its recommended repair.

`RevisedMain.lean` makes the smallest semantic repair: its conclusion is the
pair of exact answers

* every continuous self-map of the fourfold projective-plane wedge has a fixed
  point; and
* the standard polygon model `Surface false 4` admits a continuous
  fixed-point-free self-map.

The real projective plane is the repo's explicit standard polygon model
`Surface false 1` (`StatementSurfaceModels.RealProjectivePlane`).  The
fourfold wedge is an iterated use of the honest coinduced-topology quotient
`PointWedgeQuotient.Wedge`; `Surface false 4` is the repo's named standard
model of `#⁴ RP²`.  No hypothesis carries either desired conclusion.

Degenerate checks:

* The fourfold wedge is nonempty: its displayed wedge point gives a concrete
  inhabitant.  A constant self-map therefore has a fixed point, as expected.
* The `N₄` clause asserts existence rather than universal fixed-point freedom;
  the identity and constant maps do have fixed points, so changing the
  quantifier to `∀` would be false.
* The proposed `N₄ → N₃` cover is connected and its deck map is explicitly
  required to be nonidentity.  This excludes both failure modes of the generic
  deck argument (a disconnected total space, or the identity deck map).
* The grader's objection survives no longer: both requested spaces and both
  yes/no conclusions occur literally in the repaired theorem.

## Definitions

`T99A03.twoWedgePoint` is the common point of the first binary wedge.
`T99A03.FourProjectivePlanesWedge` wedges two copies of that two-plane wedge at
their common points, hence contains exactly four copies of `RP²`.
`T99A03.FourProjectivePlanesConnectedSum` and
`T99A03.ThreeProjectivePlanesConnectedSum` abbreviate `Surface false 4` and
`Surface false 3`.

All imported construction-target files used here are sorry-free.  In
particular, `PointWedgeQuotient.lean`, `StatementSurfaceModels.lean`,
`Surfaces.lean`, and `RationalLefschetz.lean` provide definitions and elementary
quotient facts, but do not pretend to supply the missing homology,
classification, or fixed-point theorem.

## Remaining lemmas

### `t99A03_wedge_lefschetz_number` — LIBRARY

**Statement.** Every continuous self-map of the concrete fourfold `RP²` wedge
has rational Lefschetz number `1` in the honest singular-homology definition
from `ConstructionTargets.RationalLefschetz`.

**Why true.** `RP²` has zero reduced rational homology.  Apply reduced
Mayer–Vietoris for a point wedge repeatedly to obtain zero reduced rational
homology for the fourfold wedge.  Consequently only `H₀ ≅ ℚ` contributes, and
every self-map acts as the identity on `H₀`, so the alternating trace is `1`.
The topology worklist already records the foundations
`projectivePlane_rationalReducedHomology_zero` and
`projectivePlaneWedge_rationalHomology`; the latter must be iterated once more
for this fourfold model.  `RationalLefschetz.lean` is the closest sorry-free
construction, but currently supplies vocabulary only.

**Estimate.** LIBRARY program, 700–1500 lines after the shared projective-plane
and point-wedge homology foundations land.

**Depends on.** No other blueprint lemma.

**Truth check.** By hand, over `ℚ`, each positive homology group of `RP²`
vanishes and reduced homology takes point wedges to direct sums.  Four zero
summands remain zero.  In degree zero the connected wedge gives one copy of
`ℚ`; the induced map of any self-map is identity on that copy.  The constant
map and the identity map both therefore have Lefschetz number `1`.

### `t99A03_wedge_fixed_point_of_lefschetz` — LIBRARY

**Statement.** If all self-maps of this fourfold wedge have Lefschetz number
`1`, then all of them have a fixed point.

**Why true.** The wedge is a finite compact polyhedron.  Apply the rational
Lefschetz fixed-point theorem to each `f`; its supplied value is `1 ≠ 0`.
The topology worklist's exact missing shared theorem is
`ConstructionTargets.LefschetzCompactPolyhedron.fixedPointOfNonzeroLefschetz`
(also recorded under the older name
`lefschetz_fixed_point_compact_polyhedron`).  This is a genuine 2000+ line
foundation, so the blueprint states it once instead of manufacturing small
proxy lemmas.  The homology conclusion is an argument, allowing this program
to run in parallel with the preceding one.

**Estimate.** LIBRARY program, 2000–5000 lines for the shared fixed-point
theorem, then a 30–60 line specialization proving that this quotient is the
required finite polyhedron.

**Depends on.** Receives the conclusion of
`t99A03_wedge_lefschetz_number` as a hypothesis; it does not depend on that
lemma's proof.

**Truth check.** The assumed Lefschetz number is exactly `1`, so the nonzero
premise is immediate.  The fourfold wedge is a finite CW complex with one
vertex and four finite `RP²` summands.  The check includes the endpoint case
of a constant map: its constant value itself is a fixed point.

### `t99A03_exists_N4_deck_involution` — LIBRARY

**Statement.** There is a connected covering `N₄ → N₃` together with a
nonidentity deck homeomorphism of `N₄`.

**Why true.** Present
`π₁(N₃) = ⟨a,b,c | a²b²c²=1⟩` and send `a` to the nonzero element of `Z/2`,
with `b,c` sent to zero.  The kernel is normal of index two.  Realize it as a
connected regular double cover.  Its Euler characteristic is
`2 χ(N₃) = -2`, and it is nonorientable because the kernel contains the
orientation-reversing loop `b`.  Surface classification identifies the total
space with `N₄`; transport the nontrivial deck transformation across that
homeomorphism.  The closest sorry-free files are
`PolygonSurfacePiOne.lean`, `Surfaces.lean`, and
`SurfaceClassification.lean`.  The missing program is the combined
covering-subgroup realization plus polygon-cover normal form; the topology
audit records the analogous large steps as `permutation_polygon_cover` and
`cover_model_homeomorph_normal_form`.

**Estimate.** LIBRARY program, 1000–2500 lines, mostly explicit polygon-cover
construction and classification transport.

**Depends on.** No other blueprint lemma.

**Truth check.** The relator maps to
`2·1 + 2·0 + 2·0 = 0` in `Z/2`, so the character is well-defined and
surjective.  The index-two kernel contains `b`, hence is nonorientable.  Its
Euler characteristic is `-2`, and `2-g=-2` forces `g=4`.  The nonzero element
of the deck group is not the identity.  This directly checks the grader's
requested example rather than assuming the desired fixed-point-free map.

### `t99A03_deckTransformation_fixedPointFree` — already proved

**Statement.** A nonidentity deck homeomorphism of a connected covering has no
fixed point.

**Why true.** If it fixed `x`, compare it with the identity map as two lifts of
`p`.  `IsCoveringMap.eq_of_comp_eq`, connectedness, and equality at `x` make
the two lifts equal, contradicting nonidentity.

**Estimate.** 12 lines; included with a complete proof, so no seat is needed.

**Depends on.** Only Mathlib's covering-map API.

**Truth check.** Connectedness is essential: on a disconnected trivial cover,
a deck map can be the identity on one component and nontrivial elsewhere, so
it may have fixed points.  The lemma includes `[ConnectedSpace E]`.  If the
deck map is identity, `hne` fails.  Thus both degenerate counterexamples are
excluded exactly where needed.

## Dependency layers

* **Layer 1 (parallel):** `t99A03_wedge_lefschetz_number` (LIBRARY),
  `t99A03_wedge_fixed_point_of_lefschetz` (LIBRARY, taking the first
  conclusion as a hypothesis), and `t99A03_exists_N4_deck_involution`
  (LIBRARY).  The generic deck lemma is already proved.
* **Layer 2:** `apm_t99a03`, a sorry-free assembly from the three Layer 1
  conclusions and the proved deck lemma.

There are **three open lemmas**, all honestly marked LIBRARY foundations.
The principal doubt is scheduling, not truth: the compact-polyhedron Lefschetz
theorem and explicit polygon-cover identification are both much larger than a
normal lemma seat.

## Compilation and axioms

Both Lean files compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t99A03/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t99A03/Blueprint.lean
```

The final output of `#print axioms apm_t99a03` was:

```text
'apm_t99a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The three warnings are exactly the three LIBRARY lemmas.  The generic deck
lemma and the main theorem contain no `sorry`.
