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

### Split of `t99J05_lefschetz_euler`

`T99J05CPHomologyProfile n X` says exactly that rational homology is finite
dimensional and has finrank one in even degrees at most `2*n`, zero otherwise.
The banked `RP3Homology.rationalMayerVietoris` is generic in the ambient space,
so the CP² file supplies the previously missing rational MV foundation.  Its
`CP2` abbreviation is definitionally the same `Space ℂ 2` as `CP 2` here.

* `t99J05_lefschetz_euler_cover` (40–70 lines, independent): proves openness
  and coverage.  Generalize `cp_open_cover_aux_coord`/`cp_open_cover`; use
  `affineSource_isOpen`, `Projectivization.rep_nonzero`, and `Fin.lastCases`.
* `t99J05_lefschetz_euler_V` (80–120 lines, independent): constructs the
  affine-chart homeomorphism and derives the point homology profile.  Generalize
  `cpV_homology_aux_homeomorph`; then use `Homeomorph.contractibleSpace`,
  `CoefficientH0.h0Iso`, and `CoefficientContractiblePair.higher_zero`.
* `t99J05_lefschetz_euler_U` (120–150 lines, independent): constructs the
  deformation retraction which linearly kills the last coordinate.  Generalize
  `cpU_homology_aux_cpU_hequiv_CP1_*`, then transport homology with
  `CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv`.
* `t99J05_lefschetz_euler_inter` (100–150 lines, independent): identifies the
  overlap with punctured `ℂ^(n+1)`, applies
  `PuncturedNormedSpaceRadialEquivalence.unitSphereHomotopyEquivPuncturedSpace`,
  and transports banked sphere homology.  Its last conjunct is the honest H₀
  inclusion injectivity required by MV; generalize `cpUV_pathConnected` and
  `cp_mvI_zero_injective_aux_h0_map`.
* `t99J05_lefschetz_euler_step` (120–150 lines, independent given its explicit
  hypotheses): applies `RP3Homology.rationalMayerVietoris`,
  `LinearMap.ker_eq_bot`, `LinearMap.range_eq_top`, and
  `LinearEquiv.ofBijective`.  The top class comes from the connecting
  isomorphism in degree `2*n+1`; middle even classes pass through `mvJ`.
* `t99J05_lefschetz_euler_base` (30–50 lines, independent): `CP 0` is a
  singleton/projective point; use path-connected H₀ and contractibility.
* `t99J05_lefschetz_euler_trace` (100–150 lines, independent given the profile
  and homotopy): unfold `HasLefschetzNumber` and `HasEulerCharacteristic`, use
  singular-homology functor homotopy invariance, trace of the identity, and
  `Finset.sum_ite` over even degrees.

All seven leaves state claims consumed by the assembly; none is a scope marker.
For `n=0`, the step computes `CP¹`: the overlap is `S¹`, its degree-one class
connects isomorphically to H₂(CP¹), and H₁(CP¹)=0.  Thus the displayed
odd-sphere degree `2*n+1` and top CP degree `2*n+2` have the correct low-degree
behavior.  Empty exceptional-degree cases are handled by the `if` profiles;
the degree-zero injectivity prevents a spurious H₁ class.

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
