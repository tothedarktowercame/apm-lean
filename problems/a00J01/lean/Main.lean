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
  simp only [Real.rpow_zero] at this
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
-- eventually ‖f‖_p ≥ C for any C < ‖f‖_∞. The proof below handles
-- the ENNReal↔ℝ coercion bridge through `toReal`.
lemma lower_bound {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (α : ℝ≥0∞) (hα : α < eLpNorm f ⊤ (volume.restrict (Icc 0 1))) :
    ∀ᶠ p in atTop, α ≤ eLpNorm f p (volume.restrict (Icc 0 1)) := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let g := hf.mk f
  have hfg : f =ᵐ[μ] g := hf.ae_eq_mk
  have hg : StronglyMeasurable g := hf.stronglyMeasurable_mk
  obtain ⟨β, hαβ, hβ⟩ := exists_between hα
  have hβ_top : β ≠ ⊤ := ne_of_lt (hβ.trans_le le_top)
  let s := {x | β < ‖g x‖ₑ}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hg.measurable.enorm
  have hμs : μ s ≠ 0 := by
    intro hzero
    have hae : ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ β := by
      rw [ae_iff]
      simpa only [s, Set.mem_setOf_eq, not_le] using hzero
    have hgb : eLpNorm g ⊤ μ ≤ β := by
      simpa only [eLpNorm_exponent_top] using
        (eLpNormEssSup_le_of_ae_enorm_bound hae)
    have hfb : eLpNorm f ⊤ μ ≤ β :=
      (le_of_eq (eLpNorm_congr_ae hfg)).trans hgb
    exact (not_le_of_gt hβ) hfb
  have hμs_top : μ s ≠ ⊤ := by
    apply ne_of_lt
    calc
      μ s ≤ μ Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := by
        simp only [μ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
      _ < ⊤ := ENNReal.one_lt_top
  have hμs_real : 0 < (μ s).toReal := ENNReal.toReal_pos hμs hμs_top
  have hβ_real : α.toReal < β.toReal :=
    ENNReal.toReal_strict_mono hβ_top hαβ
  have hlim :
      Tendsto (fun n : ℕ => β.toReal * (μ s).toReal ^ (1 / (n : ℝ)))
        atTop (𝓝 β.toReal) := by
    simpa using
      tendsto_const_nhds.mul (tendsto_rpow_inv_nat_atTop (μ s).toReal hμs_real)
  have hevent :
      ∀ᶠ n : ℕ in atTop, α.toReal <
        β.toReal * (μ s).toReal ^ (1 / (n : ℝ)) :=
    (tendsto_order.1 hlim).1 α.toReal hβ_real
  obtain ⟨n, hnpos, hn⟩ :
      ∃ n : ℕ, 0 < n ∧
        α.toReal < β.toReal * (μ s).toReal ^ (1 / (n : ℝ)) :=
    ((eventually_gt_atTop (0 : ℕ)).and hevent).exists
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  have hn_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hα_prod :
      α ≤ β.toNNReal • μ s ^ (1 / (n : ℝ≥0∞).toReal) := by
    apply (ENNReal.toReal_le_toReal (ne_top_of_lt (hαβ.trans hβ))
      (ENNReal.mul_ne_top (by simp [hβ_top]) (ENNReal.rpow_ne_top_of_nonneg
        (one_div_nonneg.2 ENNReal.toReal_nonneg) hμs_top))).1
    simpa [ENNReal.smul_def, ENNReal.toReal_mul, hβ_top, hμs_top,
      ENNReal.toReal_rpow, ENNReal.coe_toNNReal_eq_toReal] using hn.le
  have hlevel :
      ∀ᵐ x ∂μ, x ∈ s → β.toNNReal ≤ ‖g x‖₊ := by
    filter_upwards [] with x hx
    change β < ‖g x‖ₑ at hx
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal hβ_top]
    exact le_of_lt hx
  have hn_lower : α ≤ eLpNorm g (n : ℝ≥0∞) μ :=
    hα_prod.trans
      (le_eLpNorm_of_bddBelow hn0 hn_top β.toNNReal hs hlevel)
  letI : IsProbabilityMeasure μ := ⟨by
    simp only [μ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩
  filter_upwards [eventually_ge_atTop (n : ℝ≥0∞)] with p hp
  calc
    α ≤ eLpNorm g (n : ℝ≥0∞) μ := hn_lower
    _ ≤ eLpNorm g p μ :=
      eLpNorm_le_eLpNorm_of_exponent_le hp hg.aestronglyMeasurable
    _ = eLpNorm f p μ := (eLpNorm_congr_ae hfg).symm

end LowerBound

section MainTheorem

theorem eLpNorm_tendsto_top {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (_hf_top : eLpNorm f ⊤ (volume.restrict (Icc 0 1)) < ⊤) :
    Tendsto (fun p : ℝ≥0∞ => eLpNorm f p (volume.restrict (Icc 0 1)))
      atTop (nhds (eLpNorm f ⊤ (volume.restrict (Icc 0 1)))) := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by
    simp only [μ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩
  apply tendsto_order.2
  constructor
  · intro α hα
    obtain ⟨β, hαβ, hβ⟩ := exists_between hα
    filter_upwards [lower_bound hf β hβ] with p hp
    exact hαβ.trans_le hp
  · intro β hβ
    filter_upwards [] with p
    exact (eLpNorm_le_eLpNorm_of_exponent_le (le_top : p ≤ ⊤) hf).trans_lt hβ

end MainTheorem

end ApmCanaries.Frames.A00J01.Apm_v2_a00J01_1774990935426.Main
