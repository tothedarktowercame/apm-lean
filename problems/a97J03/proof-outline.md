# Proof Outline: a97J03

## Problem

Let 1 < p, q < ∞ with 1/p + 1/q = 1. For f ∈ L^p(ℝ), g ∈ L^q(ℝ),
define h(y) = ∫ f(y-x)g(x)dm(x). Prove h is continuous and vanishes at ±∞.

## Strategy

1. Hölder: |h(y)| ≤ ‖f‖_p · ‖g‖_q (uniform bound).
2. Continuity: |h(y)-h(y')| ≤ ‖τ_{y-y'}f̌ - f̌‖_p · ‖g‖_q → 0 (L^p translation continuity).
3. Vanishing: approximate by C_c functions, transfer via Hölder bound.

## Proved (exit 0, 0 sorries)

The definition and complete theorem compile. Closer hop 3 recovered the
previous real-valued implementation from git history, compared it with the
frozen complex-valued statement, and specialized the scalar-polymorphic
argument to `ℂ`. The decisive implementation was reused from the compiled
neighboring bundle `a03J03`:

1. `Lp.compMeasurePreserving` makes translated Lp representatives continuous.
2. `ContinuousLinearMap.lpPairing`, instantiated with
   `ContinuousLinearMap.mul ℂ ℂ`, identifies the complex pairing with the
   frozen convolution integral.
3. Compact-support density and the pairing norm give uniform approximation.
4. Compact support gives cocompact vanishing, which restricts to ±∞.

## Phase-A hints used
- #1 `e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density`:
  cited; confirms strategy (Hölder + C_c density for vanishing).
- #5 `math-informal/monotone-approximation`: cited; C_c density underlies approximation.

## Phase-A hints dropped
- #2 (review of #1): same content as #1.
- #3 (`e-j02-translation-symmdiff-preimage-api`): cited in boundary comments; provides API direction.
- #4 (`e-j02-steinhaus-positive-convolution-open-locus`): different convolution context.
- #6 (`e-codexpilot-integral-minkowski-eLpNorm-bochner`): Minkowski, not Hölder.
- #7 (`e-codexpilot-probe-the-high-risk-integral-assembly`): process hint, noted.

## Mid-solve lookups

1. Mathlib `Analysis/Convolution.lean` explicitly lists general Lp/Lq
   continuity as TODO; no direct theorem was available. Discarded as a direct route.
2. Prior solved `problems/a03J03/lean/Main.lean` contained axiom-clean compiled
   continuity and cocompact-vanishing proofs for the identical integral; reused.
3. Mathlib `Function/Holder.lean` supplied `lpPairing` and its integral identity; used.
4. Mathlib `Data/Real/ConjExponents.lean` supplied
   `Real.holderConjugate_iff`; used to convert the frozen hypotheses.
5. Mathlib order-compactness source supplied `atTop_le_cocompact` and
   `atBot_le_cocompact`; used.
6. Git commits `1f93f86`, `69e3274`, and `ab95ab5` showed why the earlier
   completed real proof was restored and isolated the reusable proof body;
   used without changing the frozen theorem statement.
