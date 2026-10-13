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

## Shared analytic lemmas

All four are standalone holes.

### `apm_m98A06_duBoisReymond` (A)

**Statement.** On every positive interval, stationarity is equivalent to
admissibility plus the representation `A cos x + B sin x` on the interval.
**Sketch.** Test against compactly supported smooth variations, obtain
`y''+y=0` distributionally, and use the regularity of a distributional
solution with continuous first derivative.  The converse is integration by
parts.  **Estimate:** 100–150 lines.  **Check:** constants `A,B`, including
`A=B=0`, directly solve the ODE; the endpoint equations remain explicit in
admissibility.

### `apm_m98A06_wirtinger` (B)

**Statement.** The scaled sharp Wirtinger inequality on `[0,L]` for every
endpoint-zero `C¹` function, together with equality iff the function is a
multiple of `sin(πx/L)` on the interval.  **Sketch.** Scale to `[0,π]` and
integrate the square of the standard first-order transform; track its zero
case.  **Estimate:** 100–150 lines.  **Check:** the zero function and all
first sine multiples give equality; the second sine mode gives strict
inequality.  The assumption `0<L` excludes the degenerate interval.

### `apm_m98A06_weak_FTC` (C)

**Statement.** If `(u,du)` satisfies the custom `InH10Pi` predicate, then
`u(x)=∫₀ˣdu` for every `x∈[0,π]`.  **Sketch.** The distributional weak
derivative and `L²` bound give the absolutely continuous integral
representative; continuity identifies it pointwise and the trace at zero
sets the constant.  **Estimate:** 80–140 lines.  **Check:** `u=du=0` and
`u=sin`, `du=cos` satisfy the formula, including both endpoints.

### `apm_m98A06_sine_computations` (D)

**Statement.** Bundles the general Dirichlet sine mode's admissibility and
energy, and the normalized modes on `[0,π]` with their classical derivative,
weak membership, unit norm, and energy `k²-1`.  **Sketch.** Differentiate,
use the integer-multiple sine endpoint identities, and evaluate the standard
sine/cosine square integrals.  **Estimate:** 100–150 lines.  **Check:** `k=1`
has energy zero; `k=2` has energy three.  `k≠0` prevents the impossible
normalization of the zero mode.

## Independent conclusion assemblies

These seven holes take the relevant shared facts as explicit hypotheses;
therefore none has another admitted theorem among its axioms.

* `apm_m98A06_stationary_resonant_classification_of_duBoisReymond` takes A;
  solve the two endpoint equations at `2π`. **Estimate:** 30–50 lines.
  **Check:** the free sine coefficient is visible directly.
* `apm_m98A06_stationary_nonresonant_classification_of_duBoisReymond` takes
  A; zero kills the cosine coefficient and nonresonance fixes the sine
  coefficient. **Estimate:** 30–60 lines. **Check:** at `a=π/2` the answer is
  `sin x`.
* `apm_m98A06_resonant_no_global_extrema_of_sine_computations` takes D and
  uses quadratic dominance with positive and negative modes. **Estimate:**
  50–90 lines. **Check:** the compiled half-frequency and double-frequency
  examples have opposite energy signs.
* `apm_m98A06_nonresonant_energy_geometry_of_facts` takes B and D, combines
  them with the already-proved stationary energy split, and selects low/high
  modes. **Estimate:** 80–130 lines. **Check:**
  `((kπ/a)²-1)a/2` has the required signs on either side of `π`.
* `apm_m98A06_weak_poincare_and_equality_of_facts` takes B, C, D; transfer
  the weak pair to its absolutely continuous representative, then apply the
  sharp inequality and normalization. **Estimate:** 80–140 lines. **Check:**
  normalized first modes are exactly the two equality cases.
* `apm_m98A06_constrained_energy_unbounded_above_of_sine_computations` takes
  D and chooses `k` with `k²-1>M`. **Estimate:** 30–50 lines. **Check:** the
  displayed energy tends to infinity.
* `apm_m98A06_poincare_best_constant_of_facts` takes B, C, D; B+C prove that
  one works and D's first mode forces every valid constant to be at least
  one. **Estimate:** 50–90 lines. **Check:** both first-mode square integrals
  coincide.

The original seven names are now proved, without direct `sorry`, by applying
these assemblies to A–D.

## Dependency layers

* **Layer 1 (parallel, eleven seats):** A–D and all seven `_of_...` assembly
  lemmas.  Assemblies receive A–D as ordinary hypotheses, so they can land in
  any order and do not inherit another seat's `sorryAx`.
* **Layer 2 (proved assembly):** the original seven theorem names.
* **Layer 3 (proved assembly):** bridges 2 and 3.
* **Layer 4 (proved assembly):** `apm_m98a06`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m98A06/Blueprint.lean
```

The final output was:

```text
'apm_m98a06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The eleven warnings for `sorry` are exactly the eleven Layer 1 lemmas.
Neither an original conclusion theorem, a bridge, nor the main theorem
contains a direct `sorry`.

## Doubt

All statements match standard one-dimensional variational theory and I am
convinced they are true.  The main risk is that B or C may approach the upper
end of the estimate because pinned Mathlib has no packaged sharp interval
Poincaré theorem for this bespoke weak-derivative predicate.  Their statements
are now isolated, so that risk is no longer duplicated across conclusions.
