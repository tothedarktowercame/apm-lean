# t95A04 blueprint: the Veronese embedding of RP²

## Triage

Verdict: **true and faithful**.  The registered theorem says exactly that the
printed even quadratic map on `Sphere 2` descends to the fixed real-projective
quotient, is smooth, is a topological embedding, and is an immersion in
Mathlib's local-normal-form sense.  This matches the sentence in `problem.md`.

I tried the relevant degenerate cases before retaining the statement:

* The zero vector cannot occur because the source is the unit sphere.
* Points with two zero coordinates are handled by the square coordinate at the
  remaining nonzero coordinate.  More generally, the already proved theorem
  `RealProjectiveVeroneseFibers.veroneseSphereMap_eq_iff` explicitly selects a
  nonzero coordinate and therefore covers every pattern of zero coordinates.
* The map is unchanged at the antipode, since every printed coordinate is a
  product of two coordinates.  Hence the formula is well-defined on RP².
* At a coordinate-axis point, the derivative still has rank two on the sphere
  tangent plane: for example at `(1,0,0)`, tangent vectors `(0,a,b)` map to the
  two cross-term directions `(a,b)`.

The topology worklist's former atlas/descent blockers have been discharged in
the sorry-free modules `RealProjectiveSmoothTarget`,
`RealProjectiveEvenQuadraticDescent`, and `RealProjectiveVeroneseFibers`.
There was no t95A04 solve-loop cache or t95A04 solve-loop ledger row to reuse.

## Reused results (already proved)

The blueprint imports the following sorry-free construction targets:

* `rpSmoothAtlas` and `sphereProjectionEvenMapSmoothDescent` provide the atlas
  and smooth quotient descent.
* `veroneseDescended_sphereProjection` identifies the descended map with the
  six printed coordinates.
* `veroneseDescended_contMDiff` proves smoothness.
* `veroneseDescended_injective` proves injectivity, including all zero-coordinate
  cases.

The compactness theorem and embedding adapter in `Blueprint.lean` are also
proved, not assigned as holes.  Compactness is the continuous image of compact
`Sphere 2`; `Continuous.isClosedEmbedding` then turns continuous injectivity
from this compact space into an embedding in the Hausdorff Euclidean target.

## Assigned lemmas

### 1. `t95A04_veroneseDescended_mfderiv_injective`

**Statement in words.**  At every point of RP², the manifold derivative of the
descended Veronese map is injective.

**Why true.**  Lift the point to `p : Sphere 2` and use the banked local
diffeomorphism for `sphereProjection`.  For an ambient vector `v`, the
derivative of `p ↦ ppᵀ` is `pvᵀ + vpᵀ`.  If it vanishes, multiplying by `p`
gives `v + (v · p)p = 0` because `‖p‖ = 1`; substituting this back (or taking its
inner product with `p`) gives `v = 0`.  Restriction to the sphere tangent space
is therefore injective, and composition with the inverse derivative of the
local diffeomorphism transports injectivity to RP².  Likely APIs are
`rpSmoothAtlas.quotient_localDiffeomorph`, the chain rule for `mfderiv`, and
coordinatewise `fderiv` rules for products and `PiLp.toLp`.

**Estimate.** 120–200 lines.

**Dependencies.** None of the other assigned lemmas; it uses only the
definitions and imported construction targets.

**Truth check.**  Hand-computed the full Jacobian and checked the axis point
`p=(1,0,0)` separately.  The kernel argument uses only `p ≠ 0`, which is forced
by sphere membership.

### 2. `t95A04_injective_clm_has_four_complement`

Extend an injective `L : E 2 →L[ℝ] E 6` to `e : E 2 × E 4 ≃L[ℝ] E 6`, with
`e (v,0)=L v`.  Estimate: 60–120 lines.  Use `Submodule.exists_isCompl`,
`Submodule.prodEquivOfIsCompl`, `LinearEquiv.ofInjective`, dimension formulas
(`finrank_range_eq`, `finrank_prod`, `finrank_euclideanSpace`), and
`LinearEquiv.toContinuousLinearEquiv` (all spaces are finite-dimensional).
The zero-dimensional pathology does not occur: the dimensions are fixed at
2, 4, and 6, and injectivity forces the range to have dimension 2.

### 3. `t95A04_writtenInExtChart_hasFDerivAt`

Identify the derivative of `writtenInExtChartAt` at the charted base point
with `mfderiv`.  Estimate: 25–50 lines.  Use
`ContMDiffAt.mdifferentiableAt`, `MDifferentiableAt.mfderiv`,
`veroneseDescended_contMDiff.contMDiffAt`, and the source/base-point simp lemmas
for `extChartAt`.  There is no boundary case: an extended chart is defined on
the whole model space and the base point lies in its genuine chart source.

### 4. `t95A04_augmented_hasFDerivAt`

Differentiate `G(v,k)=g(v)+e(0,k)` and show its derivative is `e`, assuming
`e(v,0)=L v`.  Estimate: 30–60 lines.  Use `HasFDerivAt.add`,
`hasFDerivAt_fst`, `hasFDerivAt_snd`, `ContinuousLinearMap.hasFDerivAt`, and
extensionality on pairs.  This statement is valid at every `a`, including
`a=0`; it is affine-linear in the complement coordinate.

### 5. `t95A04_augmented_contDiffAt`

Prove smoothness near `(extChartAt ... x x,0)` of the same augmented map.
Estimate: 35–70 lines.  Use the chart-coordinate smoothness furnished by
`contMDiff_iff` for `veroneseDescended_contMDiff`, then
`ContDiffAt.fst`, continuous-linear smoothness, and `ContDiffAt.add`.
Explicitly shrink to the extended-chart target if the API requires it.

### 6. `t95A04_augmented_local_inverse`

Turn a smooth map with derivative a continuous linear equivalence into a
`PartialDiffeomorph` agreeing locally with it.  Estimate: 80–140 lines.
Copy the proved pattern from `t99J04`: principally
`apm_t99J04_euclid_local_inverse`, whose proof uses
`ContDiffAt.toOpenPartialHomeomorph`,
`ContDiffAt.mem_toOpenPartialHomeomorph_source`, and smoothness of the inverse.
This leaf takes smoothness and the derivative identity as explicit hypotheses,
so it is independent of leaves 2–5.  No empty-neighbourhood issue occurs since
the returned source explicitly contains `a`.

### 7. `t95A04_isImmersionAt_of_augmented_local_inverse`

Convert the supplied local inverse of `G` into Mathlib's local normal form for
`veroneseDescended` at `x`.  Estimate: 100–150 lines.  Unfold only through
`Manifold.IsImmersionAt`; construct `IsImmersionAtOfComplement (E 4)` via
`IsImmersionAtOfComplement.mk_of_continuousAt`.  The domain chart is the
original extended chart restricted by the slice `k=0`; the codomain chart is
the inverse-function chart composed with `e`.  Use
`PartialDiffeomorph.toOpenPartialHomeomorph`, maximal-atlas lemmas for
`extChartAt`, and `q.left_inv`/the hypothesis `hqG` for the written-in-charts
equation.  The complement and all local-inverse facts are explicit hypotheses,
so this is parallel with every earlier leaf.  Sign convention is `+e(0,k)`;
on `k=0` it reduces exactly to the original map.

### 8. `t95A04_isImmersion_of_isImmersionAt`

Package pointwise `IsImmersionAt` into `IsImmersion`.  Estimate: 5–15 lines.
Use the definition/theorem for `Manifold.IsImmersion` (it is pointwise).  This
leaf is wholly independent and covers an empty source automatically.

The former library lemma `t95A04_isImmersion_of_injective_mfderiv` is now a
sorry-free assembly of leaves 2–8.  Each leaf accepts prior conclusions as
ordinary hypotheses where needed, so proving one leaf never imports another
leaf's `sorryAx`.

## Dependency layers

* **Layer 0 (done):** atlas, smooth descent, exact fibers/injectivity,
  compactness, and the compact-to-Hausdorff embedding adapter.
* **Layer 1 (parallel):** lemma 1 and all seven new leaves 2–8.
* **Layer 2 (assembly, done):** instantiate the split leaves and combine them
  with the imported smoothness/formula results and proved embedding adapter.

## Compilation and axioms gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t95A04/Blueprint.lean
```

Result: success, with warnings only on the two assigned `sorry` bodies.

`#print axioms apm_t95a04` output:

```text
'apm_t95a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem has no `sorry`; `sorryAx` enters only through the two assigned
top-level lemmas.
