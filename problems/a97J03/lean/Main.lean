/-
! # APM a97J03: Convolution of L^p and L^q functions lies in C₀

Let 1 < p, q < ∞ with 1/p + 1/q = 1, f ∈ L^p(ℝ), g ∈ L^q(ℝ).
Define h(y) = ∫ f(y-x)g(x)dm(x). Prove h is continuous and
lim_{y→±∞} h(y) = 0.

## Strategy (from informal-solution.md)

1. Hölder's inequality gives |h(y)| ≤ ‖f‖_p · ‖g‖_q (uniform bound).
2. Continuity: |h(y) - h(y')| ≤ ‖τ_{y-y'}f̌ - f̌‖_p · ‖g‖_q → 0 by L^p continuity of translation.
3. Vanishing at infinity: approximate f, g by C_c functions; their convolution has compact support;
   the Hölder bound controls the approximation error uniformly.

## Phase-A hints used
-- (Memory: e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density)
--    Prior attempt at same problem; strategy name confirms: Hölder bound + C_c density.
-- (Memory: math-informal/monotone-approximation) C_c density in L^p underlies the approximation.

## Boundary

The proof structure is fully laid out. The remaining bridges are:

1. **Hölder bound**: Showing |∫ f(y-x)g(x)| ≤ eLpNorm(f, p) · eLpNorm(g, q).
   Requires: Hölder's inequality applied to the shifted function x ↦ f(y-x).
   APIs searched: `MeasureTheory.integral_mul_le_eLpNorm`, `eLpNorm`.
   -- (Memory: e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density)
   --    confirms this is the first step.

2. **L^p continuity of translation**: Showing ‖τ_t f - f‖_p → 0 as t → 0.
   Requires: either direct proof via C_c density or finding Mathlib's translation-continuity lemma.
   APIs searched: `tendsto_eLpNorm`, `Lp.tendsto_Lp_iff_tendsto_eLpNorm'`.
   -- (Memory: e-j02-translation-symmdiff-preimage-api) provides symmetric-difference API for this.

3. **C_c density for vanishing at infinity**: Approximating f, g ∈ L^p by C_c functions,
   showing compact-support convolution vanishes outside bounded sets, transferring across approximation.

Routes NOT investigated:
- Using Mathlib's `Convolution.convolution` directly (different argument order)
- Using `ContinuousLinearMap` API for the Hölder bound
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Filter Set Topology
open scoped ENNReal Convolution

noncomputable section

namespace APMa97J03

/-- The convolution h(y) = ∫ f(y-x)g(x)dm(x).
    This matches the problem statement's definition. -/
def conv (f : ℝ → ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x, f (y - x) * g x ∂volume

/-- Main theorem: for f ∈ L^p, g ∈ L^q with 1/p + 1/q = 1 (1 < p,q < ∞),
    h = f * g is continuous and vanishes at infinity.

    -- (Memory: e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density)
    --    Strategy: Hölder bound + L^p translation continuity + C_c density for vanishing at infinity.
    -- (Memory: math-informal/monotone-approximation) C_c density approximates L^p functions. -/
theorem convolution_continuous_vanishes
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1/p + 1/q = 1)
    (f : ℝ → ℝ) (g : ℝ → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Continuous (conv f g) ∧
    Tendsto (conv f g) atTop (𝓝 0) ∧
    Tendsto (conv f g) atBot (𝓝 0) := by
  -- Step 0: h is well-defined and uniformly bounded by Hölder
  -- |h(y)| ≤ ‖f‖_p · ‖g‖_q for all y
  -- -- (Memory: e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density)
  --    The Hölder bound is the first step, doing double duty for continuity and vanishing.
  have h_bound : ∀ y : ℝ, ‖conv f g y‖ ≤
      (eLpNorm f (ENNReal.ofReal p) volume).toReal * (eLpNorm g (ENNReal.ofReal q) volume).toReal := by
    sorry

  -- Step 1: h is continuous via L^p continuity of translation
  -- |h(y) - h(y')| ≤ ‖τ_{y-y'}f̌ - f̌‖_p · ‖g‖_q → 0
  -- -- (Memory: e-j02-translation-symmdiff-preimage-api) translation continuity via symmetric differences.
  have h_continuous : Continuous (conv f g) := by
    sorry

  -- Step 2: h vanishes at ±∞ via C_c density
  -- -- (Memory: math-informal/monotone-approximation) C_c functions approximate L^p functions.
  have h_vanish_top : Tendsto (conv f g) atTop (𝓝 0) := by
    sorry

  have h_vanish_bot : Tendsto (conv f g) atBot (𝓝 0) := by
    sorry

  exact ⟨h_continuous, h_vanish_top, h_vanish_bot⟩

#print axioms APMa97J03.convolution_continuous_vanishes

end APMa97J03
