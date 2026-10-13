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
prove nullity of the *critical* frontier image and then combine it with the
interior result.

### B1. Relative critical rank strata

lean: `withinCriticalRankStratum` and
`withinCriticalSet_eq_iUnion_rankStrata` : definitions and equality for
`{x ∈ s | ¬ Function.Surjective (fderivWithin ℝ f s x)}` indexed by
the finite rank of `fderivWithin ℝ f s x`

uses: Mathlib `LinearMap.finrank_range`, finite-dimensional rank bounds

status: planned

Define the rank strata using the ambient continuous linear map returned by
`fderivWithin`.  Finite dimensionality bounds every deficient rank by the
target finrank, so the critical set is a finite (hence countable) union.  This
step does not replace the within derivative by an ordinary derivative.

### B2. Compact exhaustion of a relative rank stratum

lean: `withinCriticalRankStratum_eq_iUnion_compact` : for closed `s` and
`hf : ContDiffOn ℝ ∞ f s`, each relative rank stratum is covered by a
countable family of compact subsets on which the derivative rank is bounded
by the same index

uses: B1, Mathlib continuity of iterated within derivatives on `s`,
`SardClosedSetCompactExhaustion`

status: planned

Intersect `s` with closed balls and closed quantitative rank conditions.  The
continuity supplied by `hf` makes those conditions relatively closed; because
`s` is closed, each bounded piece is compact.  Every point enters a piece by
choosing integer bounds for its norm and the local derivative data.

### B3. Relative Taylor remainder on convex segments

lean: `ContDiffOn.uniform_taylor_remainder_on_compact_convex` : on a compact
`K ⊆ s`, with `Convex ℝ s`, `ContDiffOn ℝ n f s` gives the uniform
Taylor remainder estimates along every segment in `s` with endpoints near
`K`

uses: Mathlib `Convex.segment_subset`, within iterated derivatives, the
estimates used by `SardCompactUniformSmallTaylorRemainder`

status: planned

All difference quotients are taken along segments contained in `s`; convexity
is used exactly here.  Compactness turns the pointwise continuity of the
highest within derivative into a uniform bound.  The conclusion has the same
numerical estimate as the ambient compact Taylor lemma, with every derivative
replaced by its within version.

### B4. Relative rank-zero compact image nullity

lean: `compact_withinRankZero_image_null` : if `K ⊆ s` is compact,
`Convex ℝ s`, `s.Nonempty`, `hf : ContDiffOn ℝ ∞ f s`, and
`fderivWithin ℝ f s x = 0` on `K`, then `μ (f '' K) = 0`

uses: B3, the packing and finite-cover estimates from
`SardCompactRankZeroSmallSourceNullity`, the finite-order admissibility
inequality from `SardClassicalRegularityAdmissibility`

status: planned

Repeat the compact cube/ball covering estimate with B3.  Convexity keeps each
segment used by the estimate inside the domain.  Choose a finite differentiability
order strictly above the source/target dimension ratio from the infinity
hypothesis, then let the covering scale tend to zero.

### B5. Constant-rank coordinates relative to a convex domain

lean: `withinRank_positive_local_projected_chart` : at `x ∈ s` where
`fderivWithin ℝ f s x` has positive rank `r`, construct complementary
source and target linear coordinates and a relative local chart in which the
first `r` target coordinates are source coordinates

uses: Mathlib finite-dimensional complemented subspaces,
`HasFDerivWithinAt`, `Iff` forms of the inverse function theorem within a
convex set, and the linear packages used by
`SardComplementedDerivativeSplit`

status: planned

Split the source by the kernel and the target by the derivative range.  Apply
the inverse-function argument to the range-coordinate map, retaining the
condition that source points lie in `s`.  The conclusion is an equality on a
relative neighborhood, which is sufficient for images of subsets of `s`; no
open extension of `f` is asserted.

### B6. Relative positive-rank slice reduction

lean: `withinPositiveRank_local_image_null_of_smaller` : in B5's coordinates,
nullity of the critical image for the kernel-variable slice implies local
nullity of the rank-`r` stratum image

uses: B5, B3, `SardCompactProductImageFiberNullity`, and the smaller-source
induction hypothesis

status: planned

Fix the `r` regular coordinates.  Each remaining slice has source the
intersection of B5's relative chart image with an affine kernel fiber; it is
convex, and its closure is treated by the same relative theorem in strictly
smaller source dimension.  The projected derivative is nonsurjective on the
slice.  The product/fiber nullity theorem then assembles the slices.  This is
where positive rank decreases the induction dimension.

### B7. Compact positive-rank stratum nullity

lean: `compact_withinPositiveRankStratum_image_null` : every compact subset
of a fixed positive deficient within-rank stratum has null image

uses: B5, B6, compact finite subcovers, measure monotonicity and finite unions

status: planned

Choose B5 coordinates at every point, shrink to neighborhoods on which the
rank upper bound persists, and take a finite subcover of the compact set.
Apply B6 in every chart and combine the finitely many null images.

### B8. Closed-convex Sard induction step

lean: `closedConvex_critical_image_null_of_smaller` : assuming the closed
convex-domain theorem in every strictly smaller source finrank, prove it for
`E`

uses: B1, B2, B4, B7, countable union nullity

status: planned

Use B4 for rank zero and B7 for every positive deficient rank.  B2 converts
each stratum to countably many compact pieces; B1 covers the full critical
set by finitely many ranks.  The zero-dimensional and subsingleton-target
cases are discharged directly, matching the base cases of the banked ambient
Sard induction.

### B9. Sard on a closed convex domain

lean: `closedConvex_critical_image_null` :
`IsClosed s → Convex ℝ s → s.Nonempty → ContDiffOn ℝ ∞ f s →
  μ (f '' {x | x ∈ s ∧ ¬ Function.Surjective
    (fderivWithin ℝ f s x)}) = 0`

with finite-dimensional complete real inner-product source and target, Borel
target, and `[μ.IsAddHaarMeasure]`

uses: B8, strong induction on `Module.finrank ℝ E`

status: planned

Quantify the induction hypothesis over every source space, closed convex
domain, target, Haar measure, and smooth map of the smaller dimension.  This
allows B6's kernel coordinates to instantiate it without changing the
theorem's representation.

### B10. Model-range critical image nullity

lean: `modelRange_withinCriticalImage_null` : specialize B9 to
`s := Set.range I`

uses: B9, `I.isClosed_range`, `I.convex_range`,
`I.nonempty_interior.nonempty`

status: planned

Apply B9 directly to the chart representative.  This is the theorem consumed
by the `t01A08` manifold chart argument.  It supersedes the stronger
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
