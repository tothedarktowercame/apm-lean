# Intersection infrastructure checklist

This checklist keeps `ConstructionTargets.Intersection` driven by the APM
acceptance problems `t01A07` and `t02A06`. An item is checked only when its Lean
declaration compiles without `sorryAx`.

## Signed-count core

- [x] Transversality predicate is non-vacuous (`isTransverse_refl`,
  `not_isTransverse_zero_real`).
- [x] Local sign is derived from a determinant and is always `+1` or `-1`.
- [x] Concrete positive and negative local signs compile.
- [x] A finite intersection number is the sum of local signs.
- [x] A two-point family with opposite signs has signed count zero
  (`signedCount_finTwo_eq_zero_of_opposite`).

## Complementary tangent spaces

- [x] Canonical coordinate splitting
  `Model (p + q) ≃ₗ Model p × Model q` (`modelSplit`).
- [x] Separate left and right tangent maps (`ComplementaryTangents.left` and
  `ComplementaryTangents.right`).
- [x] Transversality is bijectivity of `(u, v) ↦ left u + right v`.
- [x] Convert a transverse tangent sum to an ambient comparison equivalence.
- [x] Standard coordinate inclusions give the identity comparison.
- [x] The direct-sum API exhibits a negative local sign.
- [x] Define product orientations from separately oriented left and right
  tangent models (`productFrame`, `productOrientation`,
  `productOrientedFrame`).
- [x] Prove swapping the two tangent factors changes the determinant and local
  sign by `(-1)^(p*q)` (`factorSwap_det`,
  `localSign_swapSourceFactors`).

## Orientations and coordinate independence

- [x] Connect determinant frames to Mathlib `Orientation` (`OrientedFrame`).
- [x] Prove frames representing the same Mathlib orientation have a
  positive-determinant transition (`OrientedFrame.transition_det_pos`).
- [x] Coherently reframe the source, ambient space, and tangent map
  (`PointDatum.reframe`).
- [x] Prove the comparison and local sign are invariant under coherent
  reframing (`PointDatum.reframe_comparison`, `localSign_reframe`).
- [x] Package separate left/right orientations into the source product frame.
- [x] Prove the packaged product frame represents the corresponding Mathlib
  orientation (`productOrientedFrame_represents`), with the independent
  standard-lines witness `productOrientation_standard_lines`.
- [x] Prove the ordered product orientation is independent of the chosen
  representative frames (`productFrame_transition_det`,
  `productOrientation_eq_of_orientation_eq`).

## Finiteness adapter

- [x] Represent the actual coincidence locus as a subtype (`Coincidence`).
- [x] Require an exact finite enumeration, preventing omitted intersection
  points (`Adapter.enumerate`).
- [x] Prove the full adapter hypothesis bundle is satisfiable with positive and
  negative singleton models.
- [ ] Optional: compact plus explicitly discrete coincidence locus implies a
  finite enumeration.
- [ ] Deferred: derive discreteness from transverse manifold derivatives.

The last two items are not needed by either initial acceptance test: both have,
or aim to construct, an explicit `Fin 2` enumeration.

## Acceptance test: `t01A07`

- [x] Problem file identifies the two projective intersection points.
- [x] Problem file constructs `Fin 2 ≃ apm_t01a07_intersection`.
- [ ] Choose projective charts around both intersection points.
- [ ] Express the quartic-surface and projective-line tangent inclusions in
  those charts.
- [ ] Build `ComplementaryTangents` at each point.
- [ ] Prove both tangent sums are transverse.
- [ ] Compute the two determinant signs and prove they are opposite.
- [ ] Replace the current mod-2 weakening with the integer signed count `0`.

This problem is the first direct-sum and sign-convention acceptance test.

## Acceptance test: `t02A06`

- [x] Problem file defines the concrete determinant/triple-product local sign.
- [x] Problem file proves antipodal points have opposite local signs.
- [x] Problem file proves two opposite signs sum to zero.
- [ ] Show distinct great-circle zero sets have nonproportional normals.
- [ ] Prove their cross product is nonzero.
- [ ] Normalize the cross product and its negative to obtain two intersection
  points.
- [ ] Prove these are all the intersection points, producing
  `Fin 2 ≃ apm_t02a06_intersection`.
- [ ] Reconcile the triple-product sign with
  `ComplementaryTangents` determinant sign.
- [ ] Close the first, non-homological conjunct of `apm_t02a06`.

The other two conjuncts of `t02A06` remain homology problems and are outside
this intersection-infrastructure track.

## Later, only when demanded by an acceptance problem

- [ ] Covering/local-diffeomorphism preservation of local signs.
- [ ] Multiplication of signed count under a finite-sheeted cover (`t01A05`).
- [ ] Boundary/cobordism invariance of intersection number (`t97A05`).
- [ ] Homotopy invariance and the homological intersection pairing (`t03J05`
  and related problems).
- [ ] Automatic extraction from a general embedded-submanifold API.
- [ ] General perturbation or parametric transversality theorem.

The final four items must not be pulled into the local signed-count layer merely
to make the API look complete. They should be developed only when a selected
acceptance theorem requires them.

## Validation

Run after changing the shared module:

```sh
lake env lean ConstructionTargets/Intersection.lean
lake env lean ConstructionTargets.lean
```

Headline theorems must have `#print axioms` audits. `sorryAx` is not accepted
for checked items.

Relevant landed commits as of 2026-08-19:

- `d5bafd9` — finite signed transverse-intersection core
- `f01d89e` — hypothesis-driven adapter
- `fef42f9` — complementary tangent maps
- `2e234fe` — coordinate/frame independence
