# Blueprint for t95J05

## Triage and repair

Verdict: **the registered statement is false, and the one-token measure repair is faithful**.

The source asks for the ordinary oriented integral of a differential form over
`ℝP³`.  Upstairs on the unit `S³`, that uses conventional Euclidean surface
measure.  The old definition

```lean
(1 / 2 : ℝ) * ∫ x, η.1 x ∂Measure.hausdorffMeasure 3
```

instead used Mathlib's raw, diameter-power Hausdorff measure.  In dimension
three this is `(6/π)` times Euclidean surface measure.  The density has
Euclidean surface integral `-2π²`, so the old quotient integral is `-6π`, not
`-π²`.  This is the counterexample identified by the statement-registry
grader.  It is also consistent with the topology-loop reduction
`IntrinsicSphereSecondMoments.projective_density_moment`, which says that the
raw density integral is minus the raw total mass.

`RevisedMain.lean` makes the smallest warranted change: it replaces
`Measure.hausdorffMeasure 3` by `μHE[3]` in `t95J05Integral`.  No mathematical
hypothesis or conclusion changes.  This is exactly conventional Euclidean
Hausdorff measure and therefore expresses the surface integral in
`problem.md`.  The grader's counterexample no longer applies: `μHE[3](S³) =
2π²`, hence the density integral is `-2π²`, and division by the double-cover
degree gives `-π²`.

The informal source's hint `vol B⁴ = π⁴/2` is itself a typo; its solution uses
the correct `π²/2`.  This does not require a Lean hypothesis.

I did not include `Refute.lean`: a genuinely unconditional compiled refutation
of the old theorem would itself require the missing numerical theorem for raw
Hausdorff mass.  The normalization calculation above is the exact hand
counterexample, not an assumption smuggled into the repaired theorem.

Degenerate checks: the sphere has fixed radius one and is nonempty; there is no
zero-radius case.  The antipodal action negates both the odd coefficient and
the normal factor, so the density is invariant.  At the coordinate poles
`±e₀` its value is `-4`, consistently on both representatives.  The odd mixed
term vanishes under reflection of coordinate zero, while the four square
moments sum to total mass.

The imported files `ConstructionTargets/IntrinsicSphereFinite.lean` and
`ConstructionTargets/IntrinsicSphereSecondMoments.lean` contain no `sorry`.
Their raw symmetry and integrability work is reused rather than reproved.

## Definitions and already proved steps

All definitions preceding the theorem are copied from `Main.lean`, except for
the repaired measure.  Antipodal invariance, existence and uniqueness of the
represented form, and the pointwise density expansion retain their compiled
proofs.  The quotient representation makes descent and uniqueness elementary;
it does not assume the integral result.

## Remaining lemmas

### `t95J05_euclideanHausdorff_unitSphere_mass` — LIBRARY

**Statement in words.** The normalized three-dimensional Euclidean Hausdorff
mass of the unit sphere in `ℝ⁴` is `2π²`.

**Why true.** Cover `S³` by its upper and lower graph charts over the unit
three-ball; the equator is `μHE[3]`-null.  Transport normalized Euclidean
Hausdorff measure through the graph charts, whose density is
`1 / sqrt (1-‖x‖²)`, and evaluate the radial ball integral.  Equivalently, a
proved polar/coarea comparison with four-dimensional volume and
`vol(B⁴)=π²/2` gives the same value.  Relevant Mathlib APIs are
`Measure.euclideanHausdorffMeasure_def` and
`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`.

The comparison is split at the genuine chart boundary into the following
three independent leaves.  The original `...compare_aux_coarea` lemma is now
a sorry-free measurable-partition assembly of their conclusions.  None of the
three leaves mentions either of the others, so they may land in any order.

#### `t95J05_unitSphere_upper_mass` — independent LIBRARY leaf

The strict cap `S³ ∩ {0 < x₃}` has normalized Hausdorff mass
`2 * volume (ball 0 1 : Set ℝ⁴)`.  Use the graph
`x ↦ (x, sqrt (1-‖x‖²))` over the open unit ball in `ℝ³`, the area formula,
and the top-dimensional normalization.  The exact APIs demonstrated by the
existing (but deliberately not imported here) library proofs are
`ConstructionTargets.C1GraphGlobalBounds.exact_area_value`,
`ConstructionTargets.SphereCapGraphDensity.fderiv_upper_density`,
`Measure.euclideanHausdorffMeasure_def`, and
`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`.  The last radial
calculation may instead use
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` and
`MeasureTheory.Measure.toSphere_apply_univ` after identifying the cap chart.

**Expected proof size:** 80–140 lines using the reusable graph APIs.  If those
APIs are inaccessible without a forbidden import, stop and expose the needed
general theorem instead of repeating a proof over 150 lines.  **Truth/edge check:** the cap is strict, so the singular boundary
is excluded; its missing equator is handled by the separate nullity leaf.  The
integrand is positive and locally integrable despite tending to infinity at
the boundary.

#### `t95J05_unitSphere_lower_mass` — independent LIBRARY leaf

The strict lower cap has the same mass.  To keep this leaf fully independent,
use its lower graph chart with
`ConstructionTargets.SphereCapGraphDensity.fderiv_lower_density` and
`ConstructionTargets.C1GraphGlobalBounds.exact_area_value`.

**Expected proof size:** 80–140 lines by the direct chart.
**Truth/edge check:** reflection preserves the ambient Euclidean metric and
exchanges the two strict inequalities exactly; no orientation sign enters a
measure identity.

#### `t95J05_unitSphere_equator_null` — independent LIBRARY leaf

The set `S³ ∩ {x₃ = 0}` has zero `μHE[3]` mass.  Parameterize it by the
isometric `Fin 3 → Fin 4` coordinate inclusion and use the lower-dimensional
Hausdorff-null theorem.  Useful APIs are
`Isometry.euclideanHausdorffMeasure_image`, `Measure.hausdorffMeasure_zero_of_dim_lt`,
and the pattern in `ConstructionTargets.SphereEquatorHausdorffNullity` /
`ConstructionTargets.SphereEquatorImageNullity` (again, do not add those
SphereCap imports to this blueprint).

**Expected proof size:** 40–90 lines.  **Truth/edge check:** this is genuinely
codimension one inside the three-dimensional surface (dimension two in the
four-dimensional ambient space), hence its three-dimensional normalized
Hausdorff measure is zero.  The set is nonempty, so the proof must be by
dimension, not by an accidental emptiness simplification.

The assembly uses the exact trichotomy `x₃>0`, `x₃<0`, `x₃=0`, proves all
pieces measurable, applies `measure_union` twice, and simplifies
`2V + 2V + 0 = 4V`.  Thus it covers boundary points once and requires no
cancellation assumptions about whether `V` is zero or infinite.

### `t95J05_inclusionPullback_integral`

**Statement in words.** Assuming only the preceding numerical normalized mass
equality, the repaired sphere integral of the explicit density is `-2π²`.

**Why true.** Rewrite the density with
`t95J05InclusionPullback_expand`, expand `μHE[3]` as its scalar multiple of
raw `μH[3]`, and apply the sorry-free theorem
`ConstructionTargets.IntrinsicSphereSecondMoments.projective_density_moment`.
That theorem already proves the mixed moment is zero and each coordinate
square contributes one quarter of raw mass.  Associativity of scalar
multiplication converts “minus raw mass” to “minus normalized mass”; use the
supplied `hmass` and ring normalization.

The mass conclusion is deliberately passed as a hypothesis.  This lets a
lemma seat prove the scalar/moment adapter in parallel with the LIBRARY seat,
without assuming its own conclusion.

**Expected size.** 30–50 lines.

**Dependencies.** The definitions, the stated `hmass` hypothesis, and
`ConstructionTargets.IntrinsicSphereSecondMoments.projective_density_moment`.

**Truth check.** Reflection in coordinate zero negates `x₁³x₀`, so that term
integrates to zero.  Permutation symmetry gives
`∫x₀² = mass/4`; multiplying by `-4` gives exactly `-mass`, hence `-2π²` under
the hypothesis.

## Assembly and dependency layers

The main theorem has no `sorry`.  It uses the already proved unique descent,
rewrites by the pullback equality, applies the integral lemma to the mass
lemma, and finishes the factor `1/2` by `ring`.

* **Layer 1 (parallel):**
  `t95J05_euclideanHausdorff_unitSphere_mass` (LIBRARY) and
  `t95J05_inclusionPullback_integral` (given the mass equality as a hypothesis).
* **Layer 2 (already compiled):** `apm_t95j05` assembly.

## Compilation and axioms

Both files compiled with the required 12 GiB systemd scope.  The output of
`#print axioms apm_t95j05` is:

```text
'apm_t95j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the repaired theorem only through the two named
top-level lemmas.
