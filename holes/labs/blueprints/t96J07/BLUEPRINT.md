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

### `apm_t96j07_local_numbers` — LIBRARY

**Statement in words.** Any continuous projective self-map satisfying the
registered diagonal action formula has intrinsic local Lefschetz numbers
`-1,+1,-1,+1` at the four coordinate points, in the exact chart-and-linking
sphere definition used by the theorem.

**Why true.** In the affine chart `x_i=1`, the map is diagonal with entries
`(j+1)/(i+1)` for `j ≠ i`.  Choose a sufficiently small closed Euclidean
ball inside the chart.  The displacement is the invertible diagonal linear map
`I-Df`; its normalization on the linking sphere has degree equal to the sign
of its determinant.  The products are `-6, 1/4, -2/27, 3/32`, giving the
four asserted integers.

This is marked LIBRARY because the registered predicate demands actual
`OpenPartialHomeomorph` charts, isolation on a closed ball, a continuous
normalized displacement map, and its action on integral singular `H₂(S²)`.
The final degree-to-determinant-sign bridge is substantially larger than one
lemma-seat session.  The closest sorry-free banked infrastructure is
`ConstructionTargets.RealProjectiveSmoothTarget` for real projective charts
and the coefficient/local-homology comparison modules; no existing sorry-free
target proves this exact normalized-sphere degree theorem.

**Expected size.** 600–1500 lines, dominated by the integral sphere-degree
library and chart packaging.

**Dependencies.** Definitions and the action-formula hypothesis only; it is
independent of the construction proof.

**Truth check.** The determinant arithmetic is compiled in
`apm_t96j07_previous_encoding`.  None of the three factors at any axis
vanishes, so the origin is isolated.  Hand multiplication gives exactly
`-6,1/4,-2/27,3/32`.

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
  `apm_t96j07_local_numbers` (LIBRARY), and
  `apm_t96j07_global_number` (LIBRARY/F2).
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

The three warnings are exactly the three named Layer 1 lemmas.  The definitions,
copied proved lemmas, and final assembly contain no direct `sorry`.

