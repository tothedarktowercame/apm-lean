# Blueprint for m98A06

## Triage

Verdict: **true and faithful**.

The source's preamble says `C¹([0,1])` although the integral and endpoint
conditions use `[0,a]`; the formalization makes the necessary minimal repair
to `C¹([0,a])`.  It distinguishes stationary curves from genuine global
extrema, which is essential at and beyond the first conjugate point.  It also
states the sharp Poincaré result for an explicit weak-derivative encoding of
`H¹₀(0,π)`.

Counterexample checks all agree with the statement:

* At `a = 2π`, `cos x + B sin x` satisfies both endpoint values for every
  `B`; the compiled negative mode `sin(x/2)` and positive mode `sin(2x)` have
  energies `-3π/4` and `3π`, so no global extremum can exist.
* The nonresonance condition excludes `a = kπ`, and the compiled lemma
  `Real.sin_ne_zero_iff` conversion gives `sin a ≠ 0`.
* For `0 < a < π`, the first Dirichlet eigenvalue `(π/a)²` exceeds one, so
  the quadratic form is positive definite.  For `a > π`, its first mode is
  negative and sufficiently high modes are positive.
* The zero function is in the encoded `H¹₀` class but is excluded by the
  normalization `∫y² = 1`.
* On `[0,π]`, the normalized functions `±sqrt(2/π) sin x` have energy zero;
  normalized higher sine modes have energy `k²-1`, showing unboundedness
  above and sharpness of constant one.

No canonical solve-loop record contains a counterexample.

## Reused completed work

The cached attempt supplies compiled proofs of the exact quadratic expansion
of the action, conversion between `deriv` and `derivWithin`, cancellation of
the mixed term for stationary curves, the resulting energy split, endpoint
admissibility of the explicit modes, and their exact energies.  These proofs
are retained rather than replaced by blueprint holes.

## Remaining lemmas

### `apm_m98A06_stationary_resonant_classification`

**Statement.** The stationary curves with `a = 2π` and endpoints `1,1` are
exactly `cos x + B sin x` on the interval.

**Sketch.** Use compactly supported smooth variations to turn the weak first
variation into `y'' + y = 0` distributionally.  Since `y` and its weak first
derivative are continuous, bootstrap to a classical solution.  Apply the
standard uniqueness formula for the harmonic oscillator; `y 0 = 1` fixes the
cosine coefficient and the endpoint at `2π` imposes no condition on `B`.
The reverse implication follows by direct differentiation and interval
integration by parts.

**Estimate:** 180–280 lines.  **Dependencies:** proved definitions/lemmas
only.  **Check:** substitution gives `y''+y=0`, `y 0=y(2π)=1`.

### `apm_m98A06_stationary_nonresonant_classification`

**Statement.** For positive nonresonant `a`, the only stationary curve with
endpoints `0,1` is `sin x / sin a`.

**Sketch.** Reuse the same fundamental-lemma/ODE argument.  The boundary at
zero kills the cosine coefficient; `sin a ≠ 0`, supplied by the compiled
nonresonance lemma, fixes the sine coefficient.  For the converse, calculate
the derivative and integrate by parts against endpoint-zero variations.

**Estimate:** 160–250 lines.  **Dependencies:** proved definitions/lemmas
only; independent of the resonant lemma.  **Check:** direct endpoint and ODE
substitution, including `a = π/2` where the candidate is simply `sin x`.

### `apm_m98A06_resonant_no_global_extrema`

**Statement.** Every admissible `1,1` curve on `[0,2π]` has another admissible
curve of lower energy and one of higher energy.

**Sketch.** Add scalar multiples of the compiled endpoint-zero negative and
positive modes.  `apm_m98A06_I_add_smul` makes each energy a quadratic
polynomial in the scalar.  Its leading coefficient is respectively negative
or positive, so a sufficiently large absolute scalar beats the arbitrary
linear cross term in the required direction.  Admissibility is preserved by
addition.

**Estimate:** 70–120 lines.  **Dependencies:** proved mode and quadratic
expansion lemmas only.  **Check:** if the base curve is stationary, the cross
term vanishes and the exact changes are already `-3π/4` and `3π`; for a
general base, quadratic dominance gives the same conclusion.

### `apm_m98A06_nonresonant_energy_geometry`

**Statement.** Below `π`, the sine candidate is the unique global minimizer
and there is no maximum; above `π`, every admissible curve has both a lower-
and a higher-energy competitor.

**Sketch.** Subtract the sine candidate from an arbitrary admissible curve.
The candidate is stationary, so the compiled energy split reduces the
difference to `Q(η)=∫(η'²-η²)`.  Prove the scaled Wirtinger inequality on
`[0,a]`, with equality only for the first sine mode.  It is strictly positive
when `a<π`.  For `a>π`, use `sin(πx/a)` for a negative direction and choose an
integer `m>a/π` for a positive mode `sin(mπx/a)`; scalar quadratic dominance
gives both competitors.  The same high modes show no maximum below `π`.

**Estimate:** 240–320 lines.  **Dependencies:** proved energy split and
nonresonant admissibility; independent of the classification lemmas.
**Check:** the mode energy has sign `((mπ/a)²-1)a/2`, which has exactly the
asserted signs.

### `apm_m98A06_weak_poincare_and_equality`

**Statement.** For the custom weak `H¹₀(0,π)` representation, normalized
energy is nonnegative, and equality holds exactly at the two normalized first
sine modes.

**Sketch.** Develop the one-dimensional weak fundamental theorem for the
continuous trace-zero representative, then prove Wirtinger's inequality by
applying nonnegativity to an appropriate first-order transform (equivalently,
use a sine-series approximation).  Track equality: vanishing of the square
forces the weak ODE `u'` relation and hence `u = c sin`; normalization gives
`c = ±sqrt(2/π)`.  Conversely compute the weak derivative and standard sine
integrals.  The source search confirmed that pinned Mathlib has no packaged
sharp interval Poincaré theorem for this bespoke predicate, so this is local
infrastructure rather than a one-line library application.

**Estimate:** 260–360 lines.  **Dependencies:** definitions only.
**Check:** normalized `±sqrt(2/π) sin` give equality; normalized `sin(2x)`
gives strictly positive energy `3`.

### `apm_m98A06_constrained_energy_unbounded_above`

**Statement.** There are globally `C¹`, normalized, trace-zero witnesses with
energy exceeding every real `M`.

**Sketch.** Choose a sufficiently large natural `k` and take
`sqrt(2/π) sin(kx)` with its classical derivative.  Verify the custom weak
derivative predicate by integration by parts, normalize with
`integral_sin_sq`, and compute energy `k²-1 > M`.

**Estimate:** 100–170 lines.  **Dependencies:** definitions and Mathlib's
compiled trigonometric integral APIs.  **Check:** `k=1` has energy zero and
the formula tends to infinity with `k`.

### `apm_m98A06_poincare_best_constant`

**Statement.** One is the least constant valid in the encoded Poincaré
inequality.

**Sketch.** Prove membership of `1` using the weak Poincaré argument.  For
minimality, test any proposed constant on `sin x` with weak derivative
`cos x`; both squared integrals equal `π/2`, forcing `1 ≤ C`.

**Estimate:** 140–220 lines.  **Dependencies:** definitions only at the Lean
statement level; it can be proved independently, though its upper-bound half
shares infrastructure with the weak Poincaré lemma.  **Check:** the first sine
mode forces equality, so every valid constant is at least one.

## Dependency layers

* **Layer 1 (parallel, seven seats):** all seven remaining lemmas above.
* **Layer 2 (already proved):** `apm_m98A06_bridge_2` combines the two ODE
  classifications; `apm_m98A06_bridge_3` combines the three Sobolev results.
* **Layer 3 (already proved):** `apm_m98a06` combines those bridges with the
  two finite-interval energy lemmas.

The weak Poincaré and best-constant seats should coordinate on any shared
auxiliary lemma after their first pass, but neither theorem statement depends
on the other's proof.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m98A06/Blueprint.lean
```

The final output was:

```text
'apm_m98a06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The seven warnings for `sorry` are exactly the seven Layer 1 lemmas.  Neither
bridge nor the main theorem contains a direct `sorry`.

## Doubt

All seven statements match standard one-dimensional variational theory and I
am convinced they are true.  The largest risk is proof size for the weak
Poincaré equality characterization because Mathlib does not provide it for
this custom weak-derivative predicate; it may exceed one session unless the
seat first factors reusable weak fundamental-theorem infrastructure.
