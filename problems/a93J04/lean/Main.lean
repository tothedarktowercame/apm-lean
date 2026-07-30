import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# APM a93J04: Lp norms converge to L∞ norm

**Problem.** If f : [0,1] → ℝ is bounded Lebesgue measurable, then
‖f‖ₚ → ‖f‖∞ as p → ∞.

## Proof

**Upper bound:** |f| ≤ ‖f‖∞ a.e. ⟹ ‖f‖ₚ ≤ ‖f‖∞ · 1^{1/p} = ‖f‖∞.
**Lower bound:** For c < ‖f‖∞, the set E_c = {|f| > c} has positive measure.
‖f‖ₚ ≥ c · m(E_c)^{1/p} → c as p → ∞.
**Combine:** lim inf ≥ ‖f‖∞ ≥ lim sup.

## Statement repair note

Uses Mathlib's `eLpNorm` (with exponent `⊤` for L∞) and `Measure.restrict`
for the measure on [0,1]. The convergence is stated via `Tendsto` along
`atTop` in the real exponent, mapped to `ℝ≥0∞` via `ENNReal.ofReal`.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory ENNReal Filter Set
open scoped Topology

namespace ApmCanaries.A93J04

/-- The L∞ norm of f equals the essential supremum of ‖f‖₊. -/
lemma eLpNorm_top_eq_essSup {α : Type*} {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace α] (f : α → E) (μ : Measure α) :
    eLpNorm f ⊤ μ = essSup (fun x => ‖f x‖₊ : α → ℝ≥0∞) μ := by
  rfl

private lemma tendsto_measure_rpow_one_div
    {m : ℝ≥0∞} (hm₀ : m ≠ 0) (hm_top : m ≠ ⊤) :
    Tendsto (fun p : ℝ => m ^ (1 / (ENNReal.ofReal p).toReal))
      atTop (𝓝 1) := by
  have h_inv : Tendsto (fun p : ℝ => 1 / (ENNReal.ofReal p).toReal)
      atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
    simp [ENNReal.toReal_ofReal hp.le, one_div]
  have hm_nnreal : m.toNNReal ≠ 0 := by
    simpa [ENNReal.toNNReal_eq_zero_iff] using ⟨hm₀, hm_top⟩
  have h_nnreal :
      Tendsto (fun p : ℝ => m.toNNReal ^ (1 / (ENNReal.ofReal p).toReal))
        atTop (𝓝 1) := by
    simpa using Filter.Tendsto.nnrpow tendsto_const_nhds h_inv (Or.inl hm_nnreal)
  convert (ENNReal.tendsto_coe_toNNReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp h_nnreal using 1
  · funext p
    simp only [Function.comp_apply]
    symm
    rw [ENNReal.coe_rpow_of_ne_zero hm_nnreal, ENNReal.coe_toNNReal hm_top]

/-- **Main theorem:** For bounded measurable f on [0,1], ‖f‖ₚ → ‖f‖∞.

    The proof combines:
    (1) Upper bound: `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` with q = ∞
        gives ‖f‖ₚ ≤ ‖f‖∞ · μ(univ)^{1/p}.
    (2) Lower bound: for c < ‖f‖∞, E_c = {|f| > c} has positive measure
        (definition of essSup). Then ‖f‖ₚ ≥ c · m(E_c)^{1/p} → c.
    (3) Both measure factors tend to one, and `tendsto_order` supplies the squeeze. -/
theorem tendsto_eLpNorm_atTop
    {α : Type*} [MeasurableSpace α] {f : α → ℝ} {μ : Measure α}
    (hf : AEStronglyMeasurable f μ)
    (hf_bdd : eLpNorm f ⊤ μ ≠ ⊤)
    (hμ_fin : μ Set.univ < ⊤) :
    Tendsto (fun p : ℝ => eLpNorm f (ENNReal.ofReal p) μ)
      atTop (𝓝 (eLpNorm f ⊤ μ)) := by
  by_cases hμ₀ : μ = 0
  · subst μ
    simp
  have hμ_top : μ Set.univ ≠ ⊤ := hμ_fin.ne
  have hμ_univ₀ : μ Set.univ ≠ 0 := by
    exact Measure.measure_univ_ne_zero.2 hμ₀
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨b, hab, hb⟩ := exists_between ha
    let s : Set α := {x | b < ‖f x‖ₑ}
    have hb_top : b ≠ ⊤ := ne_top_of_lt (hb.trans_le (le_top))
    have hs : NullMeasurableSet s μ := by
      simpa [s] using
        hf.aemeasurable.enorm.nullMeasurableSet_preimage (measurableSet_Ioi : MeasurableSet (Ioi b))
    have hμs₀ : μ s ≠ 0 := by
      intro hμs
      have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ b := by
        rw [ae_iff]
        change μ {x | ¬ ‖f x‖ₑ ≤ b} = 0
        simpa [not_le, s] using hμs
      have hnorm_le : eLpNorm f ⊤ μ ≤ b := by
        rw [eLpNorm_exponent_top, eLpNormEssSup]
        exact essSup_le_of_ae_le b hae
      exact (not_le_of_gt hb) hnorm_le
    have hμs_top : μ s ≠ ⊤ := ne_top_of_lt ((measure_mono (subset_univ s)).trans_lt hμ_fin)
    have hlower : ∀ p : ℝ, 0 < p →
        b * μ s ^ (1 / (ENNReal.ofReal p).toReal) ≤
          eLpNorm f (ENNReal.ofReal p) μ := by
      intro p hp
      have hp₀ : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hp
      have hmono :
          eLpNorm (s.indicator fun _ : α => b.toReal) (ENNReal.ofReal p) μ ≤
            eLpNorm f (ENNReal.ofReal p) μ := by
        apply eLpNorm_mono_enorm
        intro x
        by_cases hx : x ∈ s
        · rw [Set.indicator_of_mem hx]
          have hbx : b ≤ ‖f x‖ₑ := (show b < ‖f x‖ₑ from hx).le
          simpa [← ofReal_norm_eq_enorm, Real.norm_of_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hb_top] using hbx
        · simp [Set.indicator_of_notMem hx]
      calc
        b * μ s ^ (1 / (ENNReal.ofReal p).toReal) =
            ‖b.toReal‖ₑ * μ s ^ (1 / (ENNReal.ofReal p).toReal) := by
              rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg ENNReal.toReal_nonneg,
                ENNReal.ofReal_toReal hb_top]
        _ = eLpNorm (s.indicator fun _ : α => b.toReal) (ENNReal.ofReal p) μ :=
          (eLpNorm_indicator_const₀ hs hp₀ ENNReal.ofReal_ne_top).symm
        _ ≤ eLpNorm f (ENNReal.ofReal p) μ := hmono
    have htend :
        Tendsto (fun p : ℝ => b * μ s ^ (1 / (ENNReal.ofReal p).toReal))
          atTop (𝓝 b) := by
      simpa using ENNReal.Tendsto.const_mul
        (tendsto_measure_rpow_one_div hμs₀ hμs_top) (Or.inr hb_top)
    filter_upwards [htend.eventually (eventually_gt_nhds hab),
      eventually_gt_atTop (0 : ℝ)] with p hap hp
    exact hap.trans_le (hlower p hp)
  · intro a ha
    have htend :
        Tendsto
          (fun p : ℝ =>
            eLpNorm f ⊤ μ * μ Set.univ ^ (1 / (ENNReal.ofReal p).toReal))
          atTop (𝓝 (eLpNorm f ⊤ μ)) := by
      simpa using ENNReal.Tendsto.const_mul
        (tendsto_measure_rpow_one_div hμ_univ₀ hμ_top) (Or.inr hf_bdd)
    have hupper : ∀ p : ℝ,
        eLpNorm f (ENNReal.ofReal p) μ ≤
          eLpNorm f ⊤ μ * μ Set.univ ^ (1 / (ENNReal.ofReal p).toReal) := by
      intro p
      simpa using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (f := f) (μ := μ) (p := ENNReal.ofReal p) (q := ⊤) le_top hf
    filter_upwards [htend.eventually (eventually_lt_nhds ha)] with p hpa
    exact (hupper p).trans_lt hpa

end ApmCanaries.A93J04
