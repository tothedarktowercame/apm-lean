# Proof Outline: a97J03

## Problem

Let 1 < p, q < ∞ with 1/p + 1/q = 1. For f ∈ L^p(ℝ), g ∈ L^q(ℝ),
define h(y) = ∫ f(y-x)g(x)dm(x). Prove h is continuous and vanishes at ±∞.

## Strategy

1. Hölder: |h(y)| ≤ ‖f‖_p · ‖g‖_q (uniform bound).
2. Continuity: |h(y)-h(y')| ≤ ‖τ_{y-y'}f̌ - f̌‖_p · ‖g‖_q → 0 (L^p translation continuity).
3. Vanishing: approximate by C_c functions, transfer via Hölder bound.

## Proved (exit 0, 4 sorries)

Definitions: `conv` (matching problem statement) compiles.
Theorem statement compiles. Proof structure laid out with 4 sorries:

1. **h_bound** (boundary): Hölder bound |conv f g y| ≤ eLpNorm(f,p) · eLpNorm(g,q).
2. **h_continuous** (boundary): continuity via L^p translation continuity.
3. **h_vanish_top** (boundary): vanishing at +∞.
4. **h_vanish_bot** (boundary): vanishing at -∞.

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
None beyond Phase A. All Mathlib API exploration was direct source grep.
