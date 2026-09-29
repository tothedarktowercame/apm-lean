# t99J04 reroute

## Exact stall in the old route

The old route stopped before `apm_t99J04_bridge_local_inverse_function`.
Mathlib's `ContDiffAt.toOpenPartialHomeomorph` gives a Euclidean local
homeomorphism for `writtenInExtChartAt ... f`, but the route then proposed to
package both manifold charts as `PartialDiffeomorph`s and compose/conjugate
three `PartialDiffeomorph`s.  That cannot be carried out through the advertised
API: `PartialDiffeomorph` deliberately has no composition operation, and there
is no theorem promoting the chart-level object to
`IsLocalDiffeomorphAt`.  The repeated probes therefore never supplied any of
the three sorries.  In Lean terms, the first unavailable term was a
`PartialDiffeomorph (𝓘(ℝ,E)) (𝓘(ℝ,E')) X Y ⊤` whose source contains `x`, whose
`toFun` agrees with `f` there, and whose two `ContMDiffOn` fields follow from
the Euclidean inverse-function object.

## New route: compose topology, construct smooth structure directly

This route does **not** construct chart `PartialDiffeomorph`s and does not need
`PartialDiffeomorph.trans`.  It composes the already available
`OpenPartialHomeomorph`s, then uses that composite's `PartialEquiv` as the
`toPartialEquiv` field of one directly constructed `PartialDiffeomorph`.

1. Add a small coordinate extraction lemma (~15 lines): from
   `hf : ContMDiffAt 𝓘 𝓘 ⊤ f x`, obtain both
   `ContDiffAt ℝ ⊤ (writtenInExtChartAt 𝓘 𝓘 x f) (extChartAt 𝓘 x x)` and
   `HasFDerivAt (writtenInExtChartAt ...) (mfderiv 𝓘 𝓘 f x) ...`.
   For self models this is a direct use of `contMDiffAt_iff` and
   `(hf.mdifferentiableAt (by simp)).hasMFDerivAt.2`, simplifying with
   `modelWithCornersSelf_coe` and `range_id`.  This removes the old route's proposed
   hand-written fderiv/mfderiv transport.

2. Convert `hbij` to a `ContinuousLinearEquiv` with
   `ContinuousLinearEquiv.ofBijective` (or its current constructor), rewrite
   the derivative supplied by step 1 to that equivalence, and apply
   `ContDiffAt.toOpenPartialHomeomorph` to the coordinate representative
   (~15--25 lines).  This supplies the Euclidean inverse-function object `e`
   and membership of the chart point in `e.source`.

3. Form an `OpenPartialHomeomorph X Y` using only the mature topological API:
   restrict the source chart around `x`, compose `(extChartAt 𝓘 x)` with `e`,
   then compose with `(extChartAt 𝓘 (f x)).symm`; intersect/restrict the source
   so every point maps through the target chart and so `f` equals the
   composite.  `OpenPartialHomeomorph.trans` exists and handles this part
   (~35--55 lines).  Shrink once more to the open neighbourhood on which the
   original `ContMDiffAt` is `ContMDiffOn`; do not manufacture smooth chart
   wrappers.

4. Define the required `PartialDiffeomorph` as a structure literal whose
   `toPartialEquiv` is the object from step 3.  Its open fields come directly
   from the open partial homeomorphism.  Prove `contMDiffOn_toFun` pointwise
   from the shrunken `hf`; prove `contMDiffOn_invFun` pointwise by rewriting in
   the fixed source/target charts and using
   `OpenPartialHomeomorph.contDiffAt_symm` (equivalently
   `ContDiffAt.to_localInverse`) for `e` (~60--90 lines).  The standard chart
   smoothness lemmas discharge the pre/post compositions.  Apply
   `⟨phi, hx, hEqOn⟩` to close
   `apm_t99J04_bridge_local_inverse_function`.

5. Close `apm_t99J04_bridge_coordinateMap_mfderiv_bijective` independently
   (~45--70 lines): prove coordinate-map smoothness with
   `contMDiff_pi_space` followed by smoothness of `WithLp.toLp`; compute its
   `mfderiv` using the pi and continuous-linear-map composition rules; reduce
   the resulting coordinate linear map to
   `apm_t99J04_dualCoordinates_bijective`.  Split `n = 0` (subsingleton source
   and target) from `0 < n`.

6. Replace the final `sorry` (~15--25 lines): in the first conjunct apply step
   4 to the smooth coordinate map and step 5's bijectivity; in the second use
   the existing
   `apm_t99J04_surjective_of_bijective_mfderiv_of_localIFT`, passing step 4.

The new reusable construction is thus an
`openPartialHomeomorph_to_partialDiffeomorph_at` lemma taking an already
composed local homeomorphism plus forward and inverse pointwise smoothness.
This formulation matches the fields Lean actually requests and avoids the
missing `PartialDiffeomorph` composition layer entirely.

## Compiled probe

File: `/tmp/reroute-t99J04/probe.lean`

Exact command:

```text
cd /home/joe/code/apm-lean
lake env lean /tmp/reroute-t99J04/probe.lean
```

Verbatim output:

```text
```

Exit status: 0 (elapsed 4.9 seconds).  The probe compiles the exact step-1 lemma,
including both `ContDiffAt` for `writtenInExtChartAt` and `HasFDerivAt` with
the manifold derivative itself.  This specifically disproves the old route's
claim that a separate, difficult fderiv/mfderiv transport lemma is required
for self models.

Correction: the first version of this report incorrectly claimed compilation.
Its compound command began with `test -L .lake/packages`, but this checkout's
`.lake/packages` is a directory.  That test failed and `&&` short-circuited
before Lean ran.  When run directly against the pinned Mathlib, that first
probe failed on the newer name `ModelWithCorners.range_self` and a missing
argument to `ContMDiffAt.mdifferentiableAt`.  The probe now uses the pinned
names and supplies `(by simp)` for `⊤ ≠ 0`; the direct command above is the
successful rerun.

## Confidence

Moderate (0.72) for the local-IFT bridge: the riskiest derivative transport
compiled, and the remaining construction uses structure fields plus
`OpenPartialHomeomorph.trans`, not a missing smooth composition API.  The main
risk is bookkeeping while shrinking the composed source so that the inverse
smoothness proof uses fixed charts.  High (0.9) that this is genuinely a new
route and identifies a buildable next lemma.  Moderate (0.65) for complete
closure because the coordinate-map derivative still requires its own API
normalization, although it no longer blocks beginning the local-IFT work.
