# Blueprint for a96A07

## Triage verdict: true and faithful

The formal statement matches the source: `g` is analytic on a neighborhood of
the closed unit disk, injective on the unit circle, and the conclusion produces
the bounded connected open image domain with the correct frontier and a
`BijOn` restriction from the open disk.

No degenerate counterexample was found:

- a constant map is excluded because the distinct circle points `1` and `-1`
  would have the same image;
- the identity and affine maps satisfy the statement directly;
- critical points in the disk would create multiplicity greater than one and
  are ruled out by the argument-principle/Jordan proof, not by an omitted
  hypothesis;
- analyticity on a genuinely larger closed ball supplies continuity through
  the boundary and avoids one-sided extension issues.

## What “construction-blocked” meant

The 2026-08-26 classification referred to a missing **Jordan curve / planar
separation construction**. The earlier development reduced the theorem through
Rouché zero counts, angular lifts, annular strip lifts, and finally a planar
sheet-crossing theorem: an embedded circle has winding-number magnitude one
around either complementary side. The terminal historical names included
`apm_a96A07_HasJordanSecondSide`, a one-turn logarithmic-derivative integral
bound, and `apm_a96A07_HasStripUnitSheetIntersection`.

I searched the current Mathlib sources for Jordan curve, Schoenflies,
embedded-circle separation, simple-loop index, winding-number-one, Alexander
duality, and plane separation. Mathlib still has no theorem supplying this
construction. The occurrences of “Jordan” concern unrelated Jordan
decompositions/algebras. Thus the classification remains genuinely
construction-blocked; it was not merely an obsolete API search.

## Reused compiled work

The current file already proved openness, connectedness, and boundedness of
the canonical candidate `g '' disk`. The blueprint additionally restores the
following proofs from the historical development:

- `apm_a96A07_frontier_image_disk_subset`;
- `apm_a96A07_of_injOn_disk_of_boundaryImage_subset_frontier`;
- `apm_a96A07_of_injOn_closedBall`;
- `apm_a96A07_boundaryImage_disjoint_of_openEmbedding`;
- `apm_a96A07_isOpenMap_disk_restrict`;
- `apm_a96A07_of_injOn_disk`.

These compile against the current Mathlib tree. In particular, once interior
injectivity is known, open mapping makes the disk restriction an open
embedding; inverse continuity prevents a boundary value from colliding with an
interior value, and compactness gives the exact frontier equality. The main
theorem is therefore assembled with no `sorry` of its own.

## Split of the former library lemma

`apm_a96A07_injOn_disk_of_injOn_circle` is now a sorry-free assembly.  The
shared count is `apm_a96A07_diskZeroCount g w`, namely the meromorphic divisor
sum from `ConstructionTargets.Rouche.zeroCountInClosedBall` for `g-w` on the
closed unit disk.  This is an actual multiplicity count, not a predicate
defined to make the desired equality true.

All five leaves below are parallel: none mentions another new leaf.  Consumer
lemmas receive their suppliers' conclusions through ordinary hypotheses or
assemble the leaves only after all are available.

### `apm_a96A07_analyticOnNhd_sub_value` (30--50 lines)

Restrict differentiability from the larger closed ball to an open ball around
the closed unit disk, convert with `DifferentiableOn.analyticOnNhd`, and use
`AnalyticOnNhd.fun_sub analyticOnNhd_const`.  The useful Mathlib tools are
`Metric.closedBall_subset_ball`, `DifferentiableOn.analyticOnNhd`, and
`AnalyticOnNhd.fun_sub`.  The positive epsilon handles the boundary exactly;
there is no radius-zero case because the disk radius is `1`.

### `apm_a96A07_argumentPrinciple_disk` (20--40 lines)

Apply
`ConstructionTargets.Rouche.circleIntegral_logDeriv_eq_divisor_sum` with
`c=0`, `R=1`, and `f z=g z-w`; unfold `apm_a96A07_diskZeroCount`.  The
off-boundary hypothesis says precisely that `f` is nonzero on the sphere.
This leaf is independent and is already supported by the banked Rouché file.

### `apm_a96A07_jordan_one_turn_logDeriv` (LIBRARY, 200+ lines)

This is the one missing full Jordan-index statement, isolated exactly as
requested.  If the log-derivative integral of `g-w` is an integer multiple
`n·2πi`, injectivity of `g` on the circle forces `|n|≤1`.  A proof may identify
the integral with the winding of `t ↦ g(exp(it))-w`, then apply the simple
closed curve index theorem.  The banked `CircleWindingUniqueness` and
`PeriodicCircleHomotopyWinding` provide uniqueness and homotopy invariance of
the integer after an exponential lift, but neither proves the Jordan
one-turn bound.  The a97J08 grid construction produces an essential loop
around an arbitrary bounded complementary component; it likewise does not
show that the embedded boundary itself has index `±1`.  Thus it cannot close
this leaf without a further Jordan crossing theorem.

The statement deliberately permits `deriv g z = 0` at circle points.  The
logarithmic derivative may then vanish in its numerator, but has no pole on
the contour because `w` is off the boundary image.  Hence no regular-embedding
hypothesis has been silently added.

### `apm_a96A07_two_preimages_force_two_le_zeroCount` (60--100 lines)

Use `MeromorphicOn.divisor_apply` and
`AnalyticAt.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff` to put both
distinct zeros in the finite divisor support, prove each analytic order is at
least one, and bound the `finsum` by the two singleton contributions.  Useful
support/finite-sum patterns are in a97J08's
`apm_a97j08_mem_divisor_support_iff_eq_zero` and
`apm_a97j08_zeroCount_eq_sum_filter_divisor`.  Boundary zeros are excluded by
`hw`; the two supplied points are strictly in the open disk, so both are in
the closed counting disk.  Multiplicity only strengthens the conclusion.

### `apm_a96A07_perturb_double_value_off_boundary` (90--150 lines)

Choose disjoint small balls about `x` and `y`, contained in the unit disk.
The complex open-mapping theorem applied on the larger analytic ball makes
their images open neighborhoods of the common value, so their intersection
is nonempty and open.  Show the analytic circle image has empty interior and
pick `w` in that intersection outside it.  One clean route for the latter is:
the circle parametrization is continuously differentiable on the compact
interval, hence Lipschitz; its image has planar volume zero, while a nonempty
open subset of `ℂ` has positive volume.  Mathlib tools to investigate are
`AnalyticOnNhd.is_constant_or_isOpen`, compact-interval bounds for
`Continuous.deriv`, `LipschitzWith.measure_image_le`, and
`MeasureTheory.nonempty_interior`.  Boundary injectivity excludes the
constant branch.  Critical circle points cause no problem: a `C¹` curve is
still Lipschitz even where its derivative vanishes.

## Dependency layers

- **Layer 1, parallel:** the five leaves above; exactly one is marked LIBRARY.
- **Layer 2, proved:** `apm_a96A07_diskZeroCount_le_one` combines analyticity,
  argument principle, and Jordan one-turn.
- **Layer 3, proved:** `apm_a96A07_injOn_disk_of_injOn_circle` combines the
  perturbation and two-root lower bound with Layer 2.
- **Layer 4, proved:** `apm_a96A07_of_injOn_disk` and the main theorem.

## Confidence and doubt

The main doubt is still the isolated Jordan leaf.  The perturbation leaf is
also API-sensitive: Mathlib may make the `C¹`-curve-nullity proof longer than
150 lines, in which case it should be split once more into “boundary image has
empty interior” and “two local image neighborhoods overlap off that image.”
No analytic-boundary shortcut avoiding Jordan was found.  In particular,
zeros of `g'` on the circle invalidate arguments that assume a regular curve,
though they do not affect the stated one-turn theorem.

## Compile gate and axioms

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/a96A07/Blueprint.lean
```

Output of `#print axioms apm_a96a07`:

```text
'apm_a96a07' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem and both assembly lemmas have no `sorry`; `sorryAx` enters
only through the five parallel leaves above.
