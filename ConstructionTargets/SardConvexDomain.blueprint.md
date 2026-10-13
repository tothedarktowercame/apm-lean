# Blueprint: Sard on a closed convex domain

## Provenance and fixed representation

This blueprint follows the `t01A08` route audit, step 3 (boundary/corners), in
`holes/labs/topology-routes/routes-1.md`.  It supplies the part of manifold
Sard which is absent from the banked boundaryless theorem: critical values in
a chart whose source is `Set.range I` for an arbitrary
`I : ModelWithCorners ℝ E H`.

The representation is the ambient normed space `E`, the closed convex set
`s := Set.range I`, and Mathlib's `fderivWithin ℝ f s`.  No decomposition
of `frontier s` into polyhedral faces is assumed: a general model with corners
only guarantees `I.convex_range`, `I.isClosed_range`, and nonempty interior.
The blueprint therefore proves Sard directly for a closed convex domain with
nonempty interior.  It builds on:

- `ModelWithCorners.convex_range`, `ModelWithCorners.isClosed_range`, and
  `ModelWithCorners.nonempty_interior`;
- `UniqueDiffOn.uniqueDiffWithinAt` for a convex set with nonempty interior,
  and Mathlib's within-derivative congruence lemmas;
- the compact rank stratification, Taylor estimate, projected-chart, and
  countable-null assembly declarations underlying
  `SardGenuineSmoothEuclideanProbe.critical_image_null`;
- `SardGenuineSmoothEuclideanProbe.open_domain_critical_image_null` for the
  interior part already isolated in `SardConvexDomain.lean`.

The existing theorem
`modelRange_withinCriticalImage_null_of_interior_of_frontier` is bookkeeping
only.  Its hypothesis that the image of the entire frontier is null is too
strong in source dimension greater than target dimension.  The nodes below
prove nullity of the complete within-critical image directly; in particular
they do not infer anything about an image from source nullity.

### B1. Within jets on a convex set

lean: `ContDiffOn.convexWithinJet` : from `hf : ContDiffOn ℝ ∞ f s`,
produce symmetric continuous multilinear maps `J n x` for `x ∈ s`, with
`J 0 x = f x`, `J 1 x = fderivWithin ℝ f s x`, and continuity on `s`

uses: Mathlib iterated within derivatives and uniqueness on a convex set with
nonempty interior

status: planned

Use the canonical iterated within derivatives.  Nonempty interior makes `s`
a unique-differentiability set, so the jets do not depend on auxiliary
derivative witnesses.  Symmetry follows by restriction from interior points
and continuity to the boundary.

### B2. Whitney compatibility of convex within jets

lean: `ContDiffOn.convexWithinJet_isWhitney` : for every finite order `n`,
the jets from B1 satisfy the order-`n` Whitney remainder estimates on `s`

uses: B1, Mathlib `Convex.segment_subset`, one-variable Taylor formula with
integral remainder

status: planned

For `x,y ∈ s`, integrate along the segment from `x` to `y`, which remains
in `s`.  Iterating the fundamental theorem of calculus gives the Taylor
polynomial based at `x`; continuity of `J n` gives the required little-o
remainder uniformly on compact subsets.  Convexity is used only to keep this
segment in the domain.

### B3. Whitney cubes for the complement

lean: `closedSet_whitneyCubeCover` : for closed `s` in a finite-dimensional
Euclidean space, construct a countable locally finite cover of `sᶜ` by
half-open dyadic cubes whose diameter is comparable to their distance from
`s`, with a chosen nearest point of `s` for every cube

uses: finite-dimensional properness, dyadic cubes, countability of integer
lattices, distance to a closed set

status: planned

Choose maximal dyadic cubes satisfying the standard distance inequality.
Maximality gives coverage and diameter/distance comparison; bounded diameter
ratios for intersecting enlargements give local finiteness and bounded
overlap.  Properness supplies a nearest point in nonempty closed `s`.

### B4. Smooth partition subordinate to Whitney cubes

lean: `closedSet_whitneyPartition` : smooth functions `φ Q : E → ℝ`
supported in fixed enlargements of B3's cubes, locally finite on `sᶜ`, whose
sum is one there, with derivative bounds scaling as inverse cube diameter

uses: B3, a fixed smooth compactly supported bump on Euclidean space,
locally finite sums

status: planned

Rescale and translate the fixed bump to every cube, then normalize by the
locally finite positive sum.  Bounded overlap and the cube comparison prove
the derivative estimates for the normalized functions.

### B5. Whitney extension formula

lean: `whitneyExtension` : define `F = f` on `s`; off `s`, define `F x` as
the locally finite sum of `φ Q x` times the Taylor polynomial formed from B1's
jet at B3's chosen point of `s`

uses: B1, B3, B4

status: planned

The off-set definition is a finite sum in a neighborhood of every point of
`sᶜ`, hence smooth there.  The formula is coordinate-free: Taylor
polynomials evaluate continuous symmetric multilinear maps on repeated copies
of `x - a Q`, so the target may be any finite-dimensional real normed space.

### B6. Whitney extension approaches every prescribed jet

lean: `whitneyExtension_hasJetWithin` : for every `n` and `x ∈ s`, the
`n`th derivative of B5's off-set formula tends to `J n x` as its argument
tends to `x` through `sᶜ`

uses: B2, B3, B4, B5, bounded overlap and the partition derivative bounds

status: planned

Subtract the Taylor polynomial at `x`.  B2 bounds every polynomial difference;
B3 replaces cube diameter and basepoint distance by distance to `s`; B4
controls derivatives of the coefficients.  In every Leibniz term the powers
from the Whitney remainder cancel the inverse-diameter powers, leaving a
quantity tending to zero.  This avoids any claim that nonlinear coordinate
changes preserve convex fibers.

### B7. Smooth extension from a closed convex domain

lean: `ContDiffOn.exists_contDiff_extension_of_isClosed_convex` :
`IsClosed s → Convex ℝ s → s.Nonempty → ContDiffOn ℝ ∞ f s →
  ∃ F, ContDiff ℝ ∞ F ∧ Set.EqOn F f s ∧
    ∀ x ∈ s, fderiv ℝ F x = fderivWithin ℝ f s x`

uses: B1, B5, B6, gluing differentiability across a closed set

status: planned

Take B5's function.  It is smooth off `s`; B6 supplies every derivative and
its continuity at `s`, so induction on finite order proves global smoothness
and the displayed jet identities.  The equality and first-derivative identity
are the order-zero and order-one cases.

### B8. Relative critical values embed in ambient critical values

lean: `withinCriticalImage_subset_extensionCriticalImage` : for the extension
`F` from B7,
`f '' {x | x ∈ s ∧ ¬ Surjective (fderivWithin ℝ f s x)} ⊆
 F '' {x | ¬ Surjective (fderiv ℝ F x)}`

uses: B7

status: planned

For a critical `x ∈ s`, rewrite the value using `EqOn` and the derivative
using B7's first-jet identity.  The same point witnesses membership in the
ambient critical image.

### B9. Sard on a closed convex domain

lean: `closedConvex_critical_image_null` :
`IsClosed s → Convex ℝ s → s.Nonempty → ContDiffOn ℝ ∞ f s →
  μ (f '' {x | x ∈ s ∧ ¬ Function.Surjective
    (fderivWithin ℝ f s x)}) = 0`

with finite-dimensional complete real inner-product source and target, Borel
target, and `[μ.IsAddHaarMeasure]`

uses: B7, B8,
`SardGenuineSmoothEuclideanProbe.critical_image_null`, measure monotonicity

status: planned

Choose B7's global smooth extension.  Ambient Sard makes its complete critical
image null; B8 and measure monotonicity give the relative conclusion.  Thus
the difficult positive-rank argument is reused exactly once from the banked
ambient theorem, after the extension theorem has put the map in its required
representation.

### B10. Model-range critical image nullity

lean: `modelRange_withinCriticalImage_null` : transport the source to a
Euclidean space and specialize B9 to the linear image of `Set.range I`

uses: B9, `ContinuousLinearEquiv.ofFinrankEq`, `I.isClosed_range`,
`I.convex_range`, `I.nonempty_interior.nonempty`, chain rules for
`fderivWithin`

status: planned

Choose `L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))`, set
`s' := L '' Set.range I`, and apply B9 to `f ∘ L.symm` on `s'`.  Linear
homeomorphisms preserve closedness, convexity, and nonempty interior.  The
within chain rule and invertibility of `L` identify surjectivity of the two
within derivatives, while the function images are equal.  This is the theorem
consumed by the `t01A08` manifold chart argument.  It supersedes the stronger
whole-frontier-image premise in the current aggregation lemma; the interior
split remains useful as a check and for boundaryless reuse, but is not needed
to prove B10.

### B11. Consumer transport to the sup-norm target

lean: `modelRange_finTwo_criticalImage_null` : the B10 conclusion for target
`Fin 2 → ℝ` with its existing sup norm and volume measure

uses: B10, a continuous linear equivalence with
`EuclideanSpace ℝ (Fin 2)`, `SardContinuousLinearEquivImageNullity`, and
surjectivity invariance under postcomposition by a linear equivalence

status: planned

Compose the chart map with the fixed target equivalence, apply B10 in the
inner-product target, and transport nullity back.  Injectivity and
surjectivity of the equivalence identify the two critical sets exactly.  This
node feeds the already planned final `t01A08` regular-value selection.
