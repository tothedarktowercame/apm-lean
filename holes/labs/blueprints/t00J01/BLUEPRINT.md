# Blueprint for t00J01

## Triage

Verdict: **true and faithful**.

The source asks for counterexamples to three false assertions.  The registered
theorem supplies exactly those counterexamples: the concrete Klein-bottle
quotient times a circle, the identity of the metric two-sphere with Lefschetz
number `2 ≠ 1`, and the circle map induced by
`φ(θ) = θ + 2 sin θ`, with regular fibers of cardinalities three and one.
The batch registration also records the statement as graded faithful, and the
solve/topology ledgers contain no refutation.

I checked the relevant degeneracies.  The quotient and circle factors are
nonempty.  The identity really induces identity maps, so its rational traces
are `1, 0, 1`, not a detached choice of the number `2`; this branch is already
proved.  The fold is not constant and has derivative `1 + 2 cos θ`, which
changes sign.  On a fundamental interval the fiber of `1` has only the class
of `θ = 0`, while the fiber of `exp π` has three classes.  The critical points
`θ = ±2π/3` have lift-values `±(2π/3 + √3)`, which are neither selected target
modulo `2π`, so both selected values are regular.

The compiled definitions and all existing proofs from `Main.lean` are retained.
In particular, `apm_t00j01_sphere_identity_bridge` is sorry-free and uses the
already completed `ConstructionTargets.CoefficientSphereEndpoints` witnesses.
The sorry-free `CircleWindingUniqueness` and
`KleinClosedSquareOrbitInverseContinuity` construction modules are imported so
lemma seats have the existing exponential-fiber arithmetic and the endpoint of
the banked Klein quotient chain available.

## Remaining lemmas

### Klein quotient/chart split (all leaves are parallel)

#### `apm_t00j01_kleinRel_normal_form` (50–90 lines)

Every generated relation has form
`(x,y) ↦ (m + (-1)^n x, n + y)`.  Induct on `Relation.EqvGen` using
`Relation.EqvGen.rec`; the relation, reflexive, symmetric, and transitive cases
reduce to integer arithmetic, `Int.cast_add`, `zpow_add₀`/parity simplification,
and `ring`.  Alternatively transport through the already proved coordinate
model (`KleinPlaneAffineAction.coordinateAct`,
`KleinPresentedGroupCoordinateNormalForm.coordinateEquiv`).

Truth check: negative `n` is intentional; integer powers of `-1` are defined
and still equal `±1`.  The formula includes reflexivity with `m=n=0`.

#### `apm_t00j01_klein_compact` (70–120 lines)

Show the image of `[0,1]²` under the quotient map is all of the quotient, then
use `ConstructionTargets.KleinClosedSquareOrbitInverseContinuity.isCompact_closedSquare_set`,
`IsCompact.image`, and `isCompact_range`.  The imported
`KleinSquareRepresentative.exists_closedSquare_smul` and
`KleinClosedSquareOrbitQuotientEquiv.closedSquareToOrbitQuotient_surjective`
provide the fundamental-domain calculation; bridge its `SameOrbit` relation to
this file's `EqvGen` generators using `generatorA_smul`, `generatorB_smul`, and
the normal-form induction locally (do not depend on the new normal-form lemma).

Truth check: the square is nonempty and closed/bounded; boundary duplication
does not affect compactness or surjectivity.

#### `apm_t00j01_klein_connected` (30–50 lines)

The quotient map from `ℝ²` is continuous by `continuous_coinduced_rng`, is
surjective by `Quotient.mk_surjective`, and the plane is connected.  Use
`IsConnected.image` (or `isConnected_range`) and rewrite the range as `univ`.

Truth check: this avoids the false claim that the closed fundamental square
quotient is automatically connected without checking its quotient map; the
plane-domain proof has no boundary cases.

#### `apm_t00j01_klein_local_chart` (100–150 lines)

Assuming the displayed affine normal form, take an open box of radius `< 1/2`
around a lift.  The integer-coordinate bounds show no nonidentity translate of
that box meets it.  Its saturation is open (prove directly, or mirror
`KleinPlaneOrbitQuotient.quotient_preimage_image` and
`KleinPlaneOrbitQuotient.quotientMap_isOpen`).  Restrict the quotient map and
use `Homeomorph.homeomorphOfContinuousOpen` / `Homeomorph.SetCongr` plus the
standard homeomorphism `EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`.

This is the one genuinely technical chart leaf, but the group normal form is
an explicit hypothesis and hence proved independently.  Boundary points of a
chosen square need no special case: the chart is centered at a plane lift, not
cut out inside the fundamental square.  Freeness follows from the same bounds;
in particular odd vertical translation cannot fix a point because it changes
the second coordinate by a nonzero integer.

#### `apm_t00j01_circle_local_chart` (30–60 lines)

Use the punctured-circle chart around each point, rotating the standard chart
if convenient.  Relevant Mathlib tools are `Circle.exp`,
`Circle.expHomeomorph`, `Homeomorph.trans`, `IsOpen.preimage`, and
`Complex.continuous_mul`; the existing `RotatedCircleChartTransport` module is
also a model for the rotation step.

Truth check: remove the antipode, never the chart center.  `Circle` is
nonempty, and the open real interval is genuinely open.

#### `apm_t00j01_klein_circle_compact` (20–40 lines)

Given compactness of the Klein factor, obtain `CompactSpace` with
`isCompact_iff_compactSpace`, use the existing compact-space instance for
`Circle`, and apply `isCompact_univ` to the product.  The factor conclusion is
an explicit hypothesis.

#### `apm_t00j01_klein_circle_connected` (20–40 lines)

Given connectedness of the Klein factor, combine it with `isConnected_univ`
for `Circle` using `IsConnected.prod`; simplify `univ ×ˢ univ = univ`.
Both factors are nonempty, so no empty-product degeneracy occurs.

#### `apm_t00j01_klein_circle_local_chart` (70–120 lines)

Take the two supplied factor charts, use `Homeomorph.prod` on their subtype
homeomorphisms, identify the source with the product-open set, and reassociate
coordinates via `EuclideanSpace.equiv` / `EuclideanSpace.piLpCongrLeft` (or an
explicit `LinearEquiv` upgraded with `LinearEquiv.toHomeomorph`) from
`EuclideanSpace ℝ (Fin 2) × ℝ` to `EuclideanSpace ℝ (Fin 3)`.
Use `IsOpen.prod` for both source and target sets.

Truth check: product-chart membership is componentwise, and the coordinate
map is onto all three coordinates; no dimension-zero or empty-open-set case is
present.

#### `apm_t00j01_klein_quotient_charts` (assembly; sorry-free)

Combines the compactness and connectedness leaves and applies the local product
chart leaf to `apm_t00j01_klein_local_chart apm_t00j01_kleinRel_normal_form`
and `apm_t00j01_circle_local_chart`.

### Klein-product integral `H₃` split (all leaves are parallel)

The final `apm_t00j01_klein_product_H3_zero` is now sorry-free assembly.  It
uses the explicit cover obtained by deleting `-1` and `1` from the circle.

#### `apm_t00j01_circleCover_open_cover` (15–30 lines)

Prove the two product sets open and covering.  Use `isOpen_compl_singleton`,
continuity of `Prod.snd`, `IsOpen.preimage`, and `Set.eq_univ_iff_forall`.
The cover argument is just `z ≠ -1 ∨ z ≠ 1`, using `(1 : Circle) ≠ -1`.

#### `apm_t00j01_circleCover_piece_equivs` (60–120 lines)

Each punctured circle is contractible, so projection gives a homotopy
equivalence from its product with `K` to `K`.  Use stereographic/argument
coordinates (`Circle.expHomeomorph` and a rotation for the puncture),
`HomotopyEquiv.prod`, and the standard contraction of `ℝ`.

Truth check: the deleted point is not in the subtype; the contraction must be
performed in the punctured circle, not merely in the ambient plane.

#### `apm_t00j01_circleCover_intersection_equiv` (80–150 lines)

The circle with `±1` deleted is the disjoint union of its upper and lower open
semicircles, each contractible.  Build an equivalence with `Sum K K`, using
the sign of the imaginary coordinate for the component and argument charts
within each component.  Useful tools are `Homeomorph.sumCongr`,
`HomotopyEquiv.sum`, `Circle.coe_ne_zero`, and `Complex.ext_iff`.

Truth check: after deleting `±1`, imaginary part cannot vanish, so the component
test is exhaustive and disjoint; neither component is empty.

#### `apm_t00j01_klein_H2_zero` (80–150 lines)

Show the concrete twisted affine quotient has zero integral `H₂`.  The intended
route is a homeomorphism to the genus-two nonorientable polygon surface, then
`ConstructionTargets.PolygonSurfaceHomology.radialH2BoundaryKernelModuleIso`.
Compute its attaching vector as `(2,2)` (up to the library's sign/basis
convention), so `attachingBoundary` has trivial kernel over `ℤ`.  Relevant
definitions are `attachingDegree`, `attachingBoundary`, `BoundaryKernel`, and
`radialH2BoundaryKernelModuleIso`.

This is the only leaf where the twist is essential.  For the torus word the
attaching vector is zero and the conclusion is false.  The construction
library does not currently expose the homeomorphism from this exact affine
quotient to `PairingData.Space`; if that bridge cannot be completed within
150 lines, split it out as the single remaining LIBRARY foundation rather
than hiding it in this proof.

#### `apm_t00j01_klein_H3_zero` (30–70 lines)

Transport to the polygon model and use its radial open cover: both pieces and
their overlap have no homology above degrees one/two.  Useful compiled results
are `PolygonSurfaceHomology.innerHigherHomology_isZero`,
`overlapHigherHomology_isZero`, and integral Mayer–Vietoris.  Alternatively,
derive it from the two-dimensional polygon chain model once the same concrete
homeomorphism used by the `H₂` leaf is available.

#### `apm_t00j01_circleCover_pieces_H3_zero` (25–50 lines)

Given the two homotopy equivalences and `H₃(K)=0`, transfer vanishing to both
cover pieces.  Use `SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv`
and `IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero`
(or the corresponding direct module isomorphism).  All producer conclusions
are explicit hypotheses, so this leaf is independent.

#### `apm_t00j01_circleCover_intersection_H2_zero` (35–70 lines)

Given the intersection equivalence and `H₂(K)=0`, use homotopy invariance and
homology of a sum.  Follow `EmptyAndSumSingularHomology`; the relevant
additivity mechanism is the singular-chain coproduct/biproduct comparison.
Both summands vanish, hence their biproduct does too.

#### `apm_t00j01_openCover_H3_zero` (50–100 lines)

This is a generic exactness leaf.  Apply
`ConstructionTargets.IntegralOpenCoverMayerVietoris.integralMayerVietoris` in
degrees three and two.  Exactness plus zero source `H₃(U) ⊞ H₃(V)` and zero
target `H₂(U∩V)` makes `H₃(X)` zero.  The categorical closing pattern is
`ConstructionTargets.MayerVietorisExactnessIsZero.isZero_middle_of_two_exact_of_isZero_left_of_mono_right`;
the integral theorem states exactness as range/kernel equalities, so either
convert those to `ShortComplex.Exact` or prove elementwise that every class is
zero.

Truth check for the whole split: the intersection degree-two term is two
copies of `H₂(K)`, and this is visibly the sole step using nonorientability.
Replacing `K` by `T²` makes that term nonzero and correctly prevents the proof
of `H₃(T²×S¹)=0`.

### `apm_t00j01_foldRegular_pi`

**Statement.** `exp π` is regular in the statement's explicit lift sense.

**Why true.** Convert exponential equality to an integral `2π` displacement
using `CircleWindingUniqueness`.  If the derivative vanished, then
`cos θ = -1/2`, hence `θ` is congruent to `±2π/3`; substitute into
`θ + 2 sin θ` and use elementary bounds on `π` and `√3` to contradict the
target congruence.

**Expected size.** 70–130 lines.

**Dependencies.** Definitions and compiled lift/derivative lemmas only.

**Truth check.** At the evident root `π`, the derivative is `-1`.  At the two
other roots, they lie strictly away from the turning points because the local
maximum is above `π` and the local minimum below `π`.

### `apm_t00j01_foldRegular_one`

**Statement.** `1` is regular in the statement's explicit lift sense.

**Why true.** Use the same critical-point classification.  At a critical
point the lift value is congruent to `±(2π/3 + √3)`, never `0 mod 2π`.

**Expected size.** 60–110 lines.

**Dependencies.** Definitions and compiled lift/derivative lemmas only.

**Truth check.** The sole fundamental-interval root is `0`, where the compiled
derivative calculation gives `3 ≠ 0`.  Endpoint representatives `-π` and `π`
do not map to `1`.

### `apm_t00j01_foldFiberCard_pi`

**Statement.** The fiber over `exp π` has `Nat.card = 3`.

**Why true.** Represent each circle point by an angle in a half-open interval.
Split that interval at the two critical angles `±2π/3`.  Strict monotonicity
from the sign of `1 + 2 cos θ`, the intermediate value theorem, and endpoint
values show exactly one root on each of the three monotone arcs.  Exponential
fiber arithmetic removes all other `2π` translates, and an explicit
three-element equivalence finishes the `Nat.card` computation.

**Expected size.** 100–150 lines.

**Dependencies.** Definitions, `CircleWindingUniqueness`, and the compiled
lift/derivative lemmas.  It deliberately does not depend on the regularity
lemma, so both seats can proceed in parallel.

**Truth check.** `φ(π)=π`; moreover `φ(2π/3)=2π/3+√3>π`, producing the other
two crossings around the fold.  The three monotone branches have signs
`+, -, +`, so the signed count remains one while the unsigned count is three.

### `apm_t00j01_foldFiberCard_one`

**Statement.** The fiber over `1` has `Nat.card = 1`.

**Why true.** On `[-π,π]`, `θ` and `sin θ` have the same sign, so
`θ + 2 sin θ = 0` only at zero.  The exponential equality permits translates
by `2π`; the half-open representative bounds exclude every nonzero translate.
Build an equivalence of the fiber subtype with `Fin 1` and simplify its card.

**Expected size.** 70–130 lines.

**Dependencies.** Definitions, `CircleWindingUniqueness`, and the compiled
lift identity only.

**Truth check.** `θ=0` is the compiled exhibited preimage.  For `θ>0` in the
fundamental interval the lift is positive, and for `θ<0` it is negative, so
there is no second root; the two endpoints represent one circle point and map
to `exp π`, not `1`.

## Assembly and dependency layers

The main theorem contains no `sorry`: it pairs the chart lemma with the H3
lemma, reuses the completed sphere bridge, and inserts continuity plus the four
circle facts directly.

- **Layer 1 (parallel):** the eight Klein leaves
  `apm_t00j01_kleinRel_normal_form`, `apm_t00j01_klein_compact`,
  `apm_t00j01_klein_connected`, `apm_t00j01_klein_local_chart`,
  `apm_t00j01_circle_local_chart`, `apm_t00j01_klein_circle_compact`,
  `apm_t00j01_klein_circle_connected`, and
  `apm_t00j01_klein_circle_local_chart`; also
  `apm_t00j01_klein_product_H3_zero` (with the final chart conclusion as a
  hypothesis), `apm_t00j01_foldRegular_pi`,
  `apm_t00j01_foldRegular_one`, `apm_t00j01_foldFiberCard_pi`, and
  `apm_t00j01_foldFiberCard_one`.
- **Layer 2 (already compiled):** `apm_t00j01_klein_quotient_charts` assembles
  the eight Klein leaves; the main theorem then uses it with the other five
  independent leaves.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00J01/Blueprint.lean
```

The output of `#print axioms apm_t00j01` was:

```text
'apm_t00j01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The thirteen warnings identifying `sorry` are exactly the eight new Klein
leaves and the five other previously named remaining lemmas.  Both theorem
assemblies and all reused declarations have no direct `sorry`.
