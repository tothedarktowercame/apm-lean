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

### `apm_t96j07_global_number` — LIBRARY (F2)

**Statement in words.** Any projective self-map satisfying the diagonal action
formula has rational-homological Lefschetz number zero, using the actual
singular homology maps in `apm_t96j07_HasLefschetzNumber`.

**Why true.** The positive diagonal path from the identity to
`diag(1,2,3,4)` descends to a homotopy, so homotopy invariance makes the
induced maps equal to identity maps.  Rational homology of `RP³` is `Q` in
degrees 0 and 3 and zero in degrees 1 and 2.  Under corresponding bases the
two nonzero traces are both 1, hence the alternating trace is `1-1=0`.

This is the same F2 foundation family as the rational projective-space
homology and Lefschetz obligations in the t99J05/t96A06/t97J07/t99A03
blueprints.  The reusable trace definitions live in the sorry-free
`ConstructionTargets.RationalLefschetz`; what remains is the concrete
rational homology computation for real projective 3-space plus homotopy
invariance in the registered custom predicate.

**Expected size.** 700–1800 lines if the common rational `RPⁿ` homology
foundation is not yet available; 100–250 lines once it is.

**Dependencies.** Definitions and the action-formula hypothesis only.  It does
not depend on fixed-point or local-index results.

**Truth check.** The cellular rational chain complex has one generator in
degrees 0–3, with boundary multiplication alternately by 0 and 2; over
`Q`, this leaves precisely degrees 0 and 3.  The positive diagonal homotopy
never meets a singular matrix, and the resulting traces cancel.

## Assembly

Obtain `f`, its action formula, and its fixed-point characterization from the
first lemma.  Apply the local and global lemmas independently to that formula,
then package their conclusions.  The main theorem contains no `sorry`.

## Dependency layers

- **Layer 1 (parallel):** `apm_t96j07_map_fixedPoints`,
  `apm_t96j07_diagonal_link_degree`, all four
  `apm_t96j07_local_number_axis*` leaves (each receives the generic result as
  a hypothesis), and `apm_t96j07_global_number` (LIBRARY/F2).
- **Layer 2:** the already compiled, sorry-free main-theorem assembly.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96J07/Blueprint.lean
```

The final output of `#print axioms apm_t96j07` was:

```text
'apm_t96j07' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The seven warnings are `map_fixedPoints`, the five new local leaves, and
`global_number`.  The definitions, copied proved lemmas, `local_numbers`, and
final assembly contain no direct `sorry`.
