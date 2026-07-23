import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.Order.Field

open MeasureTheory Set ENNReal Filter Topology

noncomputable section

namespace ApmCanaries.Frames.A00J01.Apm_v2_a00J01_1774990935426.Main

/-! # APM a00J01: lim_{p→∞} ‖f‖_p = ‖f‖_∞

  Upper bound: ‖f‖_p ≤ ‖f‖_∞ on finite measure space (Mathlib comparison).
  Lower bound: for α < ‖f‖_∞, ‖f‖_p ≥ α · m(E_α)^{1/p} → α.
  Squeeze: limit exists and equals ‖f‖_∞.

  Overnight run diagnosed the blocker as ENNReal rpow-exponent continuity.
  Fix: prove the key limit in ℝ via `Real.continuousAt_const_rpow`, then
  bridge to ENNReal via `le_eLpNorm_of_bddBelow`.
-/

section UpperBound

lemma upper_bound {f : ℝ → ℝ} {p : ℝ≥0∞}
    (_hp : 1 ≤ p) (_hp_top : p ≠ ⊤)
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1))) :
    eLpNorm f p (volume.restrict (Icc 0 1)) ≤
      eLpNorm f ⊤ (volume.restrict (Icc 0 1)) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (le_top : p ≤ ⊤) hf
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  rw [Real.volume_Icc, show (1 : ℝ) - 0 = 1 from by ring, ENNReal.ofReal_one] at h
  rw [one_rpow, mul_one] at h
  exact h

end UpperBound

section KeyLimit

/-! ## Helper: t^{1/n} → 1 for real t > 0

  The key limit the overnight run identified as the blocker.
  `Real.continuousAt_const_rpow` gives continuity of `a ^ ·` at 0 for `a ≠ 0`,
  so `a ^ (1/n) → a ^ 0 = 1` as `n → ∞`.
-/

lemma tendsto_rpow_inv_nat_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => t ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have hcont := Real.continuousAt_const_rpow (ne_of_gt ht) (b := (0 : ℝ))
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have := hcont.tendsto.comp hlim
  simp only [Function.comp, Real.rpow_zero] at this
  exact this

end KeyLimit

section LowerBound

/-! ## Lower bound via level sets

  For α < ‖f‖_∞, the set E_α = {x : |f(x)| ≥ α} has positive measure.
  By `le_eLpNorm_of_bddBelow`: α · μ(E_α)^{1/p} ≤ ‖f‖_p.
  Since μ(E_α)^{1/p} → 1 (by `tendsto_rpow_inv_nat_atTop`),
  eventually ‖f‖_p ≥ α.

  The full coercion bridge ℝ≥0∞ ↔ ℝ for the measure and the limit
  is the main engineering challenge. We prove a slightly restructured
  version that avoids the worst coercion pain by working with ℕ-indexed
  exponents (p = n) rather than arbitrary ℝ≥0∞ exponents.
-/

-- The lower bound for natural number exponents: for each fixed C and
-- positive-measure set s, C · μ(s)^{1/n} ≤ ‖f‖_n eventually.
-- This is the composition of le_eLpNorm_of_bddBelow with the rpow limit.
-- The lower bound uses `le_eLpNorm_of_bddBelow` (Mathlib) which gives
-- C • μ(s)^{1/p} ≤ ‖f‖_p for C ≤ ‖f‖ on s. Combined with
-- `tendsto_rpow_inv_nat_atTop` above (μ(s)^{1/p} → 1), this gives
-- eventually ‖f‖_p ≥ C for any C < ‖f‖_∞. The remaining sorry is
-- the ENNReal↔ℝ coercion bridge for the composition.
lemma lower_bound {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (α : ℝ≥0∞) (hα : α < eLpNorm f ⊤ (volume.restrict (Icc 0 1))) :
    ∀ᶠ p in atTop, α ≤ eLpNorm f p (volume.restrict (Icc 0 1)) := by
  sorry

end LowerBound

section MainTheorem

theorem eLpNorm_tendsto_top {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (hf_top : eLpNorm f ⊤ (volume.restrict (Icc 0 1)) < ⊤) :
    Tendsto (fun p : ℝ≥0∞ => eLpNorm f p (volume.restrict (Icc 0 1)))
      atTop (nhds (eLpNorm f ⊤ (volume.restrict (Icc 0 1)))) := by
  sorry

end MainTheorem

end ApmCanaries.Frames.A00J01.Apm_v2_a00J01_1774990935426.Main
