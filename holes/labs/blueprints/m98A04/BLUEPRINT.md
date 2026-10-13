# Blueprint for m98A04

## Triage

Verdict: **true and faithful**.

The Lean statement uses Mathlib's actual LF-topological `TestFunction` and
`Distribution` spaces.  Lists of coordinates encode repeated partial
derivatives.  It asserts both convolution derivative identities, smoothness,
and the periodic computation `sin * cos = π sin`.  The malformed middle term
in the printed source (`∂ᵅ * φ`, with its distribution missing) is interpreted
as `(Dᵅ T) * φ`, exactly as required by the standard identity and the informal
solution.

I tried the relevant degeneracies:

* For `n = 0`, Euclidean space is a singleton.  Translation pairings are
  constant, `List (Fin 0)` has only the empty list, and the cached proof
  compiles this branch completely.
* For the zero distribution, every convolution and every distributional
  partial is zero; `apm_m98a04_translation_analytic_zero` verifies this.
* For the empty multiindex, the distributional derivative is `T` itself;
  both the direct base lemma and the general constructed derivative compile.
* A zero test function produces the zero smooth function with all derivative
  identities intact.
* At `x = 0`, the periodic formula reduces to the integral of
  `sin y * cos y`, which is zero, agreeing with `π sin 0`.

No counterexample is recorded in the canonical solve-loop files.  The
statement is not relying on a finite-dimensional replacement of the test
function topology: the cached construction explicitly passes through one
fixed compact-support stage near each translation parameter.

## Reused completed work

The best cached attempt was copied through all of its compiled results.  In
particular it already contains:

* bundled reflected translations and bundled iterated test-function
  derivatives;
* the continuous-linear construction and specification of arbitrary
  distributional partials;
* every reflection sign and the algebraic identity moving derivatives
  between `T` and `φ`;
* a common compact-support stage for translations in a unit neighborhood;
* factorization of a distribution through that stage;
* global Lipschitz bounds and uniform quadratic Taylor remainders for every
  iterated Fréchet derivative;
* the complete dimension-zero bridge, final multiindex assembly, and periodic
  integral computation.

Thus only two scalar analytic consequences of the stage estimates remain.

## Remaining lemmas

### `apm_m98a04_translation_pairing_contDiff_of_pos_dim`

**Statement in words.** In every positive dimension, pairing a distribution
with the reflected translates of any test function is a smooth scalar
function of the translation parameter.

**Why true.** Fix a parameter `x₀`.  On its closed unit ball, use
`apm_m98a04_translateReflectStage` so every translate has support in
`apm_m98a04_translationCompact φ x₀`.  For each derivative order, rewrite the
spatial iterated derivative of the stage-valued Taylor remainder using
reflection and translation of `iteratedFDeriv`.  The compiled lemma
`apm_m98a04_iteratedFDeriv_quadratic_remainder` bounds it uniformly by
`Cᵢ ‖h‖²`.  Convert this uniform estimate to every stage seminorm using
`ContDiffMapSupportedIn.seminorm_top_le_iff`; after division by `‖h‖`, the
remainder tends to zero.  This proves the stage-valued derivative formula.
Iterate it at every finite order and compose with the fixed-stage continuous
linear map from
`apm_m98a04_distribution_translateReflect_factor_stage`.  Since `x₀` was
arbitrary, the scalar pairing is `ContDiff ℝ ∞` globally.

The key named API `ContDiffMapSupportedIn.seminorm_top_le_iff` was checked in
the pinned Mathlib source; every other cited project lemma occurs earlier in
the compiling blueprint.

**Expected size.** 220–300 lines.

**Dependencies.** Definitions and proved lemmas only.  It does not depend on
the other admitted lemma.

**Truth check.** For `T = 0` the function is constant, matching the separately
compiled zero-distribution lemma.  In dimension one with `T` equal to point
evaluation at zero, the function is `x ↦ φ x`, which is smooth.  The quadratic
bound gives remainder `O(‖h‖²)` in every seminorm, hence the required
`o(‖h‖)` after division.

### `apm_m98a04_translation_pairing_fderiv_single_of_pos_dim`

**Statement in words.** In positive dimension, the derivative of the scalar
translation pairing in coordinate `i` equals the pairing with the bundled
`i`th derivative of the test function.

**Why true.** Again work locally in the fixed support stage.  For the
first-order remainder, apply the already compiled quadratic Taylor estimate
at every iterated spatial derivative order, transport it through reflected
translation, and use
`ContDiffMapSupportedIn.seminorm_top_le_iff` to obtain convergence in the
stage topology.  Compose the resulting stage-valued `HasFDerivAt` statement
with the continuous restriction of `T`.  Evaluate its derivative on
`EuclideanSpace.single i 1`, then identify the resulting test function with
`apm_m98a04_partialListTF [i] φ` using the existing `fderivCLM` application
and translation lemmas.

**Expected size.** 160–240 lines.

**Dependencies.** Definitions and proved lemmas only.  It is independent of
the smoothness lemma, so the two seats can work simultaneously.

**Truth check.** For point evaluation at zero, the formula becomes the usual
coordinate derivative identity for `φ`.  For `T = 0` both sides are zero.  The
sign is positive because differentiation is with respect to the translation
parameter `x`; the negative reflection sign occurs only when differentiating
in the test variable `y`, and the earlier compiled reflection lemmas confirm
this distinction.

## Assembly and dependency layers

* **Layer 1 (parallel):**
  `apm_m98a04_translation_pairing_contDiff_of_pos_dim` and
  `apm_m98a04_translation_pairing_fderiv_single_of_pos_dim`.
* **Layer 2 (already proved, no seat needed):**
  `apm_m98a04_translation_analytic_bridge` dispatches the zero-dimensional
  case and supplies the two Layer 1 facts to
  `apm_m98a04_translation_bridge_of_first_derivative`.
* **Layer 3 (already proved, no seat needed):**
  construction of the witnesses for the theorem and the periodic integral.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m98A04/Blueprint.lean
```

The final output of `#print axioms apm_m98a04` was:

```text
'apm_m98a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The only `sorry` warnings are the two Layer 1 lemmas.  The analytic bridge and
main theorem contain no direct `sorry`.

## Residual uncertainty

Both lemmas are mathematically standard and I am convinced their statements
are true.  The main implementation risk is ergonomic rather than logical:
rewriting full iterated Fréchet derivatives of the reflected remainder into
the exact form expected by the fixed-stage seminorm API may consume most of a
session.  The cached quantitative estimates were designed precisely for that
conversion and leave no missing analytic bound.
