import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set Filter Topology

noncomputable section

/-! # APM a03J03: f ∈ Lp, g ∈ Lq ⟹ f*g continuous and vanishes at ∞

  Proof structure:
  Part 1 (Continuity): Hölder gives |f*g(x+h)-f*g(x)| ≤ ‖τ_h f - f‖_p · ‖g‖_q.
    Translation continuity in Lp (‖τ_h f - f‖_p → 0) closes it.
  Part 2 (Vanishing): Approximate f by φ ∈ C_c. Then |f*g(x)| ≤ |φ*g(x)| + ε.
    φ*g(x) involves integration over a compact sliding window → 0 as |x| → ∞.

  Mathlib has:
  - Convolution definition: Analysis.Convolution
  - Hölder: integral_mul_le_Lp_mul_Lq_of_nonneg
  - Translation continuity: MeasureTheory.Lp.hasTranslation (partial)
  - C_c approximation in Lp: partial support
  The specific "Lp * Lq is continuous + C₀" is NOT in Mathlib.
-/

-- Part 1: Continuity of f*g
-- |f*g(x+h) - f*g(x)| ≤ ‖τ_h f - f‖_p · ‖g‖_q → 0
-- Key ingredient: translation continuity in Lp
theorem convolution_continuous {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Continuous (fun x => ∫ y, f (x - y) * g y) := by
  -- Hölder: |Δ(f*g)| ≤ ‖τ_h f - f‖_p · ‖g‖_q
  -- Translation continuity: ‖τ_h f - f‖_p → 0
  -- Composition: f*g is continuous
  sorry

-- Part 2: f*g vanishes at infinity
-- Approximate f by φ ∈ C_c, then φ*g is localized, g ∈ Lq means sliding window → 0
theorem convolution_tendsto_zero {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Tendsto (fun x => ∫ y, f (x - y) * g y) (cocompact ℝ) (nhds 0) := by
  -- Approximate f by φ ∈ C_c with ‖f-φ‖_p < ε/(2‖g‖_q)
  -- |f*g(x)| ≤ |φ*g(x)| + ε/2
  -- φ*g(x) = ∫_{x-R}^{x+R} φ(x-y)g(y)dy → 0 as |x|→∞
  -- (sliding window integral of g^q → 0)
  sorry
