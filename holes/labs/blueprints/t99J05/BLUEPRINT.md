# Blueprint for t99J05

## Triage

Verdict: **true and faithful**.

The source asks for the diagonal map with weights `1,2,3` on `CP²`, followed
by its fixed points, local Lefschetz indices, and the extension of the same
argument to `CPⁿ`.  The registered theorem states exactly that extension with
weights `i+1`; specializing to `n = 2` recovers the printed map.  It uses the
actual quotient topology, actual affine coordinate maps, and rational singular
homology rather than postulated numerical invariants.

I first checked the edge case `n = 0`.  There is one coordinate line, the
affine coordinate space is the zero vector space, the determinant of its
identity endomorphism is `1`, the local index is `1`, and `CP⁰` has Euler
characteristic `1`.  Thus the universal quantifier over `n : ℕ` introduces no
zero-dimensional counterexample.  For general `n`, all weights `i+1` are
nonzero and pairwise distinct, so no non-coordinate fixed projective line can
occur.  The solve-loop and topology ledgers record no refutation; the batch
registry also grades the statement faithful.

The sorry-free proofs of `T99J05Diagonal_homotopy_descends` and
`T99J05_affineChartConstruction` are copied into the blueprint.  Their required
construction modules are imported explicitly.  No statement repair is needed.

## Remaining lemmas

### `t99J05_map_fixedPoints`

**Statement in words.** There is a continuous self-map of `CP n` induced by
the diagonal linear map with weights `1,…,n+1`; it is homotopic to the identity,
and its fixed points are exactly the coordinate lines.

**Why true.** Take the time-one endpoint of the already proved descended
homotopy.  Its endpoint equation supplies the quotient formula and the same
homotopy, reversed if necessary, supplies `Homotopic f id`.  If a projective
class is fixed, equality in projectivization gives a nonzero scalar `a` with
`(j+1)v_j = a v_j` for every `j`.  Two nonzero coordinates would force two
distinct natural-number weights to be equal, so exactly one coordinate is
nonzero.  Conversely each coordinate line is visibly fixed.

**Expected size.** 100–150 lines.

**Dependencies.** Only the definitions block and the already proved descent
theorem.  It does not depend on either remaining admitted lemma.

**Truth check.** Besides `n = 0`, I checked vectors supported in one coordinate
(fixed) and vectors supported in two distinct coordinates (not fixed because
the two weights differ).  Nonzeroness of the diagonal image is already proved
as `t99J05Diagonal_nonzero` in the imported sorry-free construction target.

### `t99J05_localIndices_one`

**Statement in words.** Any continuous projective map satisfying the stated
diagonal quotient formula is `C¹` in every coordinate chart at the coordinate
origin, has nonzero fixed-point determinant there, and has local index `+1`.

**Why true.** In the affine chart centered at coordinate line `i`, the local
map sends coordinate `j` to `((j+1)/(i+1)) z_j`.  It is complex-linear and
hence real smooth.  The real determinant of `I-Df` is
`∏_{j≠i} |1-(j+1)/(i+1)|²`, which is strictly positive because the weights are
pairwise distinct.  Unfolding `localIndex` then gives `1`.  The formula
hypothesis is deliberately passed directly to this lemma, so a lemma seat can
prove it in parallel with construction of the map; it does not carry any part
of the local-index conclusion.

**Expected size.** 120–150 lines after isolating the affine formula and using
the finite-dimensional diagonal determinant API internally.

**Dependencies.** Definitions and `T99J05_affineChartConstruction`; logically
only the quotient formula hypothesis is needed from `t99J05_map_fixedPoints`.

**Truth check.** At `n = 0` the product is empty and equals `1`.  For `n = 2`
the three determinants are respectively `|1-2|²|1-3|² = 4`,
`|1-1/2|²|1-3/2|² = 1/16`, and
`|1-1/3|²|1-2/3|² = 4/81`; all are positive.  This also checks that weights
smaller than the center weight cause no sign error after realification.

### `t99J05_lefschetz_euler` — LIBRARY

**Statement in words.** A self-map of `CP n` homotopic to the identity has
rational Lefschetz number `n+1`, and `CP n` has rational Euler characteristic
`n+1`, using the concrete predicates in `RationalLefschetz`.

**Why true.** Compute rational singular homology of `CP n`: it is one
dimensional in degrees `0,2,…,2n` and zero otherwise, with explicit
finite-dimensional and vanishing-above-bound certificates.  Homotopy
invariance identifies the induced maps of `f` and the identity.  Every
surviving trace is `1`, all signs are positive because the degrees are even,
and the finite sum is `n+1`.  Applying the same computation directly to the
identity gives the Euler assertion.

**Expected size.** 1500–3500 lines for the missing rational `CPⁿ` homology
library, followed by roughly 250–500 lines of trace bookkeeping.  This is
intentionally one clean LIBRARY obligation, rather than fake small lemmas.

**Dependencies.** Independent of the fixed-point and local-index calculations;
it takes their eventual map only through the honest homotopy hypothesis.
The closest sorry-free banked infrastructure is
`ConstructionTargets.CoefficientSubcomplexMayerVietoris` together with
`ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence` and
`ConstructionTargets.RationalLefschetz`.  The topology-loop STOP records that
the missing bridge is the arbitrary-coefficient range-to-literal-production
comparison and its Mayer–Vietoris naturality; there is currently no
`CoefficientProductionOpenCoverMayerVietoris` module.  The analogous integral
production module is insufficient for `ModuleCat ℚ`.

**Truth check.** The hand computation gives one rational generator in every
even degree from `0` through `2n`, hence exactly `n+1` positive summands.  It
agrees with `CP⁰` (one point), `CP¹ ≃ S²` (Euler characteristic `2`), and the
printed `CP²` case (Euler characteristic `3`).  I am confident in the lemma's
mathematical truth; the doubt is purely the large missing library bridge.

## Assembly

The main theorem uses the already proved affine charts, obtains `f` and its
fixed-point description from `t99J05_map_fixedPoints`, and feeds the quotient
formula and homotopy conclusions separately to the other two lemmas.  From
`localIndex f i = 1`, `Finset.univ` has `n+1` elements, so the sum of local
indices coerced to `ℚ` is `(n : ℚ) + 1`.  Rewriting by this equality converts
the global lemma's two numerical conclusions to the exact sum-valued
conclusions in the registered theorem.  The assembly itself has no `sorry`.

## Dependency layers

* **Layer 1 (parallel):** `t99J05_map_fixedPoints`,
  `t99J05_localIndices_one`, and the LIBRARY program
  `t99J05_lefschetz_euler`.  The latter two receive the exact conclusions they
  need as hypotheses, so their seats do not need the proof of the first lemma.
* **Layer 2 (already compiled):** the sorry-free main-theorem assembly after
  all three Layer 1 results are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t99J05/Blueprint.lean
```

The final output of `#print axioms apm_t99j05` was:

```text
'apm_t99j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The three `sorry` warnings are exactly the three named Layer 1 lemmas.  The
copied foundation and final assembly contain no direct `sorry`.
