# Blueprint for t96J07

## Triage

Verdict: **true and faithful**.

The registered theorem is the repaired version of the historical statement.  Its
nonzero hypothesis encloses the entire fixed-axis equivalence, exactly as the
projective-space problem requires.  The retained theorem
`apm_t96j07_not_fixed_axis_clause` gives a compiled counterexample to the old
precedence parse at the zero vector, but that false clause is not part of the
registered theorem.

For the current statement, the diagonal matrix has positive, pairwise distinct
eigenvalues `1,2,3,4`.  It therefore induces a continuous projective
self-map, its fixed lines are precisely the four coordinate axes, and every
fixed point is nondegenerate.  The local determinant signs are
`-,+,-,+`.  The map is joined to the identity through the positive diagonal
matrices `diag(1,1+t,1+2t,1+3t)`, so it acts as the identity on rational
homology.  Since `RP³` has rational homology `Q` in degrees 0 and 3 and zero
in degrees 1 and 2, its Lefschetz number is `1-1=0`.

Degenerate cases checked: the zero vector is excluded everywhere the
projective class is formed; each axis vector is nonzero; every diagonal
coefficient stays nonzero along the homotopy; and no ratio `(j+1)/(i+1)` with
`j ≠ i` is 1.  The topology ledger records the old precedence refutation
separately from the corrected closure and gives no counterexample to this
registered statement.

The definitions and the already proved elementary vector calculation
`apm_t96j07_previous_encoding` are copied unchanged from `Main.lean`.
No statement repair is needed.

## Remaining lemmas

### `apm_t96j07_map_fixedPoints`

**Statement in words.** Construct the continuous map induced by
`diag(1,2,3,4)`, prove its exact formula on every nonzero representative, and
show that its fixed points are exactly the four coordinate lines.

**Why true.** Descend the continuous map on nonzero vectors through
projectivization.  Scalar compatibility is immediate from linearity.  Equality
of a projective class with its image gives a nonzero scalar `c` and equations
`(i+1)x_i=c x_i`.  A nonzero coordinate determines `c`; pairwise
distinctness of the four weights forces all other coordinates to vanish.
Conversely, each axis is an eigenline.

The closest sorry-free infrastructure is
`ConstructionTargets.ProjectiveQuotientDescent`,
`ConstructionTargets.ProjectiveSpaceTopology`, and the real demonstration in
`ConstructionTargets.ProjectiveConsumerLiftDemonstrations`.  These are
available through the current `Mathlib` import, but a program may import them
explicitly when integrating the proof.

**Expected size.** 100–150 lines.

**Dependencies.** Definitions only.

**Truth check.** The already proved
`apm_t96j07_previous_encoding` contains the representative-level
fixed-axis calculation.  Direct checks on a one-coordinate vector give a fixed
class, while a vector with two nonzero coordinates would require two distinct
weights to equal the same scalar.

### `apm_t96j07_diagonal_link_degree` — GENERIC LIBRARY leaf

**Statement in words.** For arbitrary diagonal coefficients `a : Fin 3 → R`
with no `a j = 1`, normalization of the displacement
`((1-a j)x_j)_j` defines a self-map of the unit two-sphere whose action on
integral `H₂` is multiplication by the sign of `∏ j, (1-a j)`.

**Proof route / exact banked tools.** Split the diagonal map into coordinate
signs and positive absolute-value scalings.  The straight-line path between
the positive diagonal scaling and the identity remains invertible, hence its
normalized sphere maps are homotopic.  Each negative coordinate contributes
the literal map
`ConstructionTargets.CoefficientCoordinateReflections.reflectionMap`;
`ConstructionTargets.CoefficientFirstReflection.all_reflections_negative`
(specialized to `R = ℤ`, `n = 2`) says its actual singular-homology map is
`-𝟙`.  Use `Functor.map_comp`, homotopy invariance of
`AlgebraicTopology.singularHomologyFunctor`, and
`CoefficientFirstReflection.topIso ℤ 1` for the orientation.  The finite
sign arithmetic is `Finset.prod_pos_iff` / `Finset.prod_neg_iff` (or a
three-coordinate `fin_cases` proof).

**Expected size.** 100–150 lines.  **Dependencies.** Definitions only; fully
independent of all four chart leaves.

**Truth checks.** `∀ j, 1-a j ≠ 0` makes the displacement nonzero on every
unit vector, so normalization is total.  `Fin 3` is nonempty and the sphere is
genuinely `S²`; there is no dimension-zero endpoint.  Zero diagonal entries
`a j = 0` are harmless.  The displacement convention is `x-Dx`, so the sign
is `det(I-D)`, not `det(D-I)`.

### `apm_t96j07_local_number_axis0` through `axis3` — four parallel leaves

**Statement in words.** Each leaf constructs the affine chart at one coordinate
axis and packages the generic diagonal link theorem into the exact
`HasLocalLefschetzNumber` predicate.  The generic theorem is an explicit
hypothesis (not a dependency), so all four seats can work in parallel with the
generic seat.

**Shared proof route / exact tools.** Use the quotient/projective chart
construction from `ConstructionTargets.ProjectiveQuotientDescent` and the
arbitrary affine-chart topology lemmas underlying
`ConstructionTargets.RealProjectiveSmoothTarget`; in chart `x_i = 1`, derive
from `hformula` that coordinate `j ≠ i` is multiplied by `(j+1)/(i+1)`.
Choose a positive radius whose closed ball lies in the chart target using
`Metric.isOpen_ball`, `Metric.closedBall_subset_ball`, and
`Metric.closedBall_zero_subset_ball`; the diagonal coordinate formula proves
the source condition and isolation.  Instantiate `hdegree`, rescale its link
by `r` (the positive factor cancels under normalization), and discharge the
three-factor signs with `norm_num` and `fin_cases`.

- `apm_t96j07_local_number_axis0`: ratios `2,3,4`, determinant
  `(1-2)(1-3)(1-4) = -6`, result `-1`. Estimated 100–150 lines.
- `apm_t96j07_local_number_axis1`: ratios `1/2,3/2,2`, determinant `1/4`,
  result `+1`. Estimated 100–150 lines.
- `apm_t96j07_local_number_axis2`: ratios `1/3,2/3,4/3`, determinant
  `-2/27`, result `-1`. Estimated 100–150 lines.
- `apm_t96j07_local_number_axis3`: ratios `1/4,1/2,3/4`, determinant `3/32`,
  result `+1`. Estimated 100–150 lines.

**Truth checks.** Every chart denominator `i+1` is positive.  Each chart target
contains zero, so a positive closed-ball radius exists.  The three ratios omit
`i`, hence none equals one and the origin is the unique fixed point on the
ball, including its boundary.  The ball is nonempty (`r > 0`), and the link
formula uses the same `x-f(x)` sign convention as the predicate.

### `apm_t96j07_local_numbers` — sorry-free assembly

Applies the generic leaf to each of the four chart leaves and forms the nested
conjunction.  It contains no `sorry`; its only `sorryAx` paths are the five new
top-level leaves.

### Global-number leaves

#### `apm_t96j07_global_positiveDiagonal_homotopy`

**Statement.** A map with the registered representative formula is homotopic
from `ContinuousMap.id` via the positive diagonal path
`diag(1, 1+t, 1+2t, 1+3t)`.

**Expected size.** 80–140 lines. **Independent:** yes; it uses only
`hformula`.  Build the cylinder map by the same quotient descent pattern as
`apm_t96j07_map_fixedPoints`.  Useful tools are
`ConstructionTargets.ProjectiveQuotientDescent.projectiveHomogeneousMapDescent`,
`ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap`,
`ContinuousMap.Homotopic`, `ContinuousMap.Homotopy`, `continuous_pi`, and
`Projectivization.mk_eq_mk_iff`.  If descent is awkward with the product
parameter, first define each projective map and prove joint continuity after
precomposition with the quotient map.

**Truth/degenerate checks.** Every coefficient `1 + i*t` is at least one for
`t ∈ I`, so the interpolated vector of a nonzero representative is nonzero.
At `t=0` the descended map is literally the identity; at `t=1` it equals `f`
by `hformula`.  Scalar compatibility holds even for negative scalars.

#### `apm_t96j07_global_HQmap_eq_id`

**Statement.** Given an explicit homotopy from the identity to `f`, every
rational singular-homology map induced by `f` is the identity.

**Expected size.** 20–50 lines. **Independent:** yes; the homotopy is an
explicit hypothesis.  Follow the already compiled use in
`apm_t96j07_diagonal_link_degree_of_parts`: use
`ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder`,
its `_zero` and `_one` endpoint lemmas, and
`ConstructionTargets.CoefficientContractiblePair.singularHomology_map_eq_of_topCatHomotopy`.
Finish the identity endpoint with `Functor.map_id` / `map_id` and unfold
`apm_t96j07_HQmap` only as needed.

**Truth check.** The conclusion is for every `k`, including degrees above the
dimension; no finite-dimensional assumption is used by homotopy invariance.

#### `apm_t96j07_global_rationalHomology_bases` — LIBRARY (F2)

**Statement.** Package actual isomorphisms showing rational singular homology
of `RP³` is `Q` in degrees 0 and 3 and zero in degrees 1 and 2.

**Expected size.** 700–1800 lines until the common rational projective-space
homology foundation exists; 30–100 lines after importing such a theorem.
This is the one intentionally retained large LIBRARY piece: splitting it into
four degree leaves would duplicate the same missing CW/singular comparison.
It is independent of `f`, the homotopy leaf, and all local-index work.

**Required foundation / tools.** Construct the standard CW chain complex with
one rational generator in degrees 0–3 and differentials `0, 2, 0`, then use a
cellular-to-singular homology comparison.  The final algebra uses that `2` is
a unit in `ℚ`, `LinearMap.ker_eq_bot`, `LinearMap.range_eq_top`, and the
homology-object API.  No current imported theorem computes singular homology
of real projective space; do not hide that comparison inside a nominally
small degree lemma.  This is the same F2 foundation family as the
t99J05/t96A06/t97J07/t99A03 blueprints.

**Truth/degenerate checks.** The cellular boundary is multiplication by `2`
in even positive degree and `0` in odd degree.  Thus over `Q`, degrees 1 and 2
vanish, while degrees 0 and 3 are one-dimensional.  The top class survives
because `RP³` is orientable (odd projective dimension).

#### `apm_t96j07_global_number_of_parts` and `apm_t96j07_global_number`

Both are sorry-free assembly.  The first receives the induced-map equality
and all four bases explicitly, rewrites the conjugated maps to identities,
and lets `simp` compute traces `1,0,0,1`.  The second supplies the three
independent leaves above.  Neither carries any hidden topology argument.

## Assembly

Obtain `f`, its action formula, and its fixed-point characterization from the
first lemma.  Apply the local and global lemmas independently to that formula,
then package their conclusions.  The main theorem contains no `sorry`.

## Dependency layers

- **Layer 1 (parallel):** `apm_t96j07_map_fixedPoints`,
  `apm_t96j07_diagonal_link_degree`, all four
  `apm_t96j07_local_number_axis*` leaves (each receives the generic result as
  a hypothesis), `apm_t96j07_global_positiveDiagonal_homotopy`,
  `apm_t96j07_global_HQmap_eq_id`, and
  `apm_t96j07_global_rationalHomology_bases` (LIBRARY/F2).
- **Layer 2:** `apm_t96j07_global_number_of_parts`,
  `apm_t96j07_global_number`, and the already compiled final assembly.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96J07/Blueprint.lean
```

The final output of `#print axioms apm_t96j07` was:

```text
'apm_t96j07' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The remaining warnings include the independent global leaves above; both
global assembly lemmas, the definitions, copied proved lemmas,
`local_numbers`, and final assembly contain no direct `sorry`.
