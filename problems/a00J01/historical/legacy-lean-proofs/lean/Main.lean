import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Set ENNReal Filter Topology

noncomputable section

namespace ApmCanaries.Frames.A00J01.Apm_v2_a00J01_1774990935426.Main

/-! # APM a00J01: lim_{p→∞} ‖f‖_p = ‖f‖_∞

  Upper bound: ‖f‖_p ≤ ‖f‖_∞ on finite measure space (Mathlib comparison).
  Lower bound: for α < ‖f‖_∞, ‖f‖_p ≥ α · m(E_α)^{1/p} → α.
  Squeeze: limit exists and equals ‖f‖_∞.
-/

-- Upper bound: ‖f‖_p ≤ ‖f‖_∞ · μ(univ)^{1/p}
-- On a probability space (μ(univ)=1), this is ‖f‖_p ≤ ‖f‖_∞.
-- Mathlib: eLpNorm_le_eLpNorm_mul_rpow_measure_univ
lemma upper_bound {f : ℝ → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1))) :
    eLpNorm f p (volume.restrict (Icc 0 1)) ≤
      eLpNorm f ⊤ (volume.restrict (Icc 0 1)) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (le_top : p ≤ ⊤) hf
  -- h : ‖f‖_p ≤ ‖f‖_⊤ * μ(univ)^{1/p - 1/⊤}
  -- μ(univ) for volume.restrict (Icc 0 1) is volume(Icc 0 1)
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  rw [Real.volume_Icc, show (1 : ℝ) - 0 = 1 from by ring, ENNReal.ofReal_one] at h
  rw [one_rpow, mul_one] at h
  exact h

-- CLOSED: Pointwise lower bound via le_eLpNorm_of_bddBelow
-- For C : ℝ≥0 and measurable s with C ≤ ‖f‖₊ a.e. on s:
-- C · μ(s)^{1/p} ≤ ‖f‖_p
-- This is Mathlib's le_eLpNorm_of_bddBelow directly.

-- Lower bound: for α < ‖f‖_∞, eventually ‖f‖_p ≥ α
-- Uses le_eLpNorm_of_bddBelow + the fact that μ(E_α)^{1/p} → 1
lemma lower_bound {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (α : ℝ≥0∞) (hα : α < eLpNorm f ⊤ (volume.restrict (Icc 0 1))) :
    ∀ᶠ p in atTop, α ≤ eLpNorm f p (volume.restrict (Icc 0 1)) := by
  -- Step 1: le_eLpNorm_of_bddBelow gives C·μ(s)^{1/p} ≤ ‖f‖_p
  --   where s = {‖f‖₊ ≥ C} and C is a NNReal version of α
  -- Step 2: μ(s) > 0 because α < ‖f‖_∞ = essSup ‖f‖
  -- Step 3: C·μ(s)^{1/p} → C·1 = C as p → ∞ (since μ(s) > 0 means μ(s)^{1/p} → 1)
  -- Step 4: eventually C ≤ ‖f‖_p
  -- Blocker: the μ(s)^{1/p} → 1 limit requires ENNReal rpow limit lemmas
  sorry

-- Main theorem: the limit is ‖f‖_∞
-- NOT in Mathlib (searched: eLpNorm_tendsto_essSup, snorm_tendsto — not found).
-- Combine upper_bound + lower_bound via squeeze.
theorem eLpNorm_tendsto_top {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (hf_top : eLpNorm f ⊤ (volume.restrict (Icc 0 1)) < ⊤) :
    Tendsto (fun p : ℝ≥0∞ => eLpNorm f p (volume.restrict (Icc 0 1)))
      atTop (nhds (eLpNorm f ⊤ (volume.restrict (Icc 0 1)))) := by
  -- Squeeze: upper_bound gives ≤ ‖f‖_∞, lower_bound gives ≥ α for all α < ‖f‖_∞
  sorry

end ApmCanaries.Frames.A00J01.Apm_v2_a00J01_1774990935426.Main
