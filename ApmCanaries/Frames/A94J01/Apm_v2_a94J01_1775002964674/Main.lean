import Mathlib
import ApmCanaries.Frames.A94J01.Apm_v2_a94J01_1775002964674.Scratch

open MeasureTheory Set Filter

noncomputable section

namespace ApmCanaries.Frames.A94J01.Apm_v2_a94J01_1775002964674.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

variable {n : ℕ}

/-- Stronger form: controls `∫_E |f|`, not just `|∫_E f|`. -/
theorem absolute_continuity_integral_norm
    {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (E : Set (Fin n → ℝ)),
      MeasurableSet E →
      volume E < ENNReal.ofReal δ →
      ∫ x in E, ‖f x‖ ∂volume < ε := by
  have hfin : ∫⁻ x, ‖f x‖ₑ ∂volume ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hf]
    exact ENNReal.ofReal_ne_top
  obtain ⟨δ, hδpos, hδ⟩ :=
    MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt
      (f := fun x : Fin n → ℝ ↦ ‖f x‖ₑ) hfin
      (by positivity : ENNReal.ofReal ε ≠ 0)
  by_cases hδtop : δ = ⊤
  · refine ⟨1, zero_lt_one, ?_⟩
    intro E _ hvol
    have hlt : volume E < δ := by
      simpa [hδtop] using
        lt_of_lt_of_le hvol (show ENNReal.ofReal 1 ≤ (⊤ : ENNReal) from by simp)
    have htail : ∫⁻ x in E, ‖f x‖ₑ ∂volume < ENNReal.ofReal ε := hδ E hlt
    have hrestrict : Integrable (fun x : Fin n → ℝ ↦ ‖f x‖) (volume.restrict E) := hf.norm.restrict
    have hreal :
        ∫ x in E, ‖f x‖ ∂volume = (∫⁻ x in E, ‖f x‖ₑ ∂volume).toReal := by
      simpa using
        (MeasureTheory.integral_norm_eq_lintegral_enorm
          (μ := volume.restrict E) hrestrict.aestronglyMeasurable)
    rw [hreal]
    exact ENNReal.toReal_lt_of_lt_ofReal htail
  · refine ⟨δ.toReal, ENNReal.toReal_pos hδpos.ne' hδtop, ?_⟩
    intro E _ hE
    have hlt : volume E < δ := by
      simpa [ENNReal.ofReal_toReal hδtop] using hE
    have htail : ∫⁻ x in E, ‖f x‖ₑ ∂volume < ENNReal.ofReal ε := hδ E hlt
    have hrestrict : Integrable (fun x : Fin n → ℝ ↦ ‖f x‖) (volume.restrict E) := hf.norm.restrict
    have hreal :
        ∫ x in E, ‖f x‖ ∂volume = (∫⁻ x in E, ‖f x‖ₑ ∂volume).toReal := by
      simpa using
        (MeasureTheory.integral_norm_eq_lintegral_enorm
          (μ := volume.restrict E) hrestrict.aestronglyMeasurable)
    rw [hreal]
    exact ENNReal.toReal_lt_of_lt_ofReal htail

/-- Absolute continuity of the Lebesgue integral. -/
theorem absolute_continuity_integral
    {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (E : Set (Fin n → ℝ)),
      MeasurableSet E →
      volume E < ENNReal.ofReal δ →
      ‖∫ x in E, f x ∂volume‖ < ε := by
  rcases absolute_continuity_integral_norm hf hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro E hE hvol
  refine lt_of_le_of_lt ?_ (hδ E hE hvol)
  simpa using
    (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict E) f)

/-- The tail integral `∫_{|f| > M} |f|` tends to `0` as `M → ∞`. -/
lemma tail_integral_tendsto_zero
    {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f volume) :
    Tendsto (fun M : ℝ => ∫ x in {x | M < ‖f x‖}, ‖f x‖ ∂volume)
      atTop (nhds 0) := by
  let F : ℝ → (Fin n → ℝ) → ℝ :=
    fun M x ↦ ({x | M < ‖f x‖}).indicator (fun y ↦ ‖f y‖) x
  have hnull : ∀ M : ℝ, NullMeasurableSet {x : Fin n → ℝ | M < ‖f x‖} volume := by
    intro M
    simpa [Set.preimage] using
      ((hf.aestronglyMeasurable.aemeasurable.norm).nullMeasurableSet_preimage
        (μ := volume) (s := Set.Ioi M) measurableSet_Ioi)
  have h_indicator :
      Tendsto (fun M : ℝ => ∫ x, F M x ∂volume) atTop (nhds 0) := by
    simpa [MeasureTheory.integral_zero] using
      (show Tendsto (fun M : ℝ => ∫ x, F M x ∂volume) atTop (nhds (∫ x, (0 : ℝ) ∂volume)) by
    refine
      (tendsto_integral_filter_of_dominated_convergence
        (μ := volume) (F := F) (f := fun _ ↦ (0 : ℝ)) (l := atTop)
        (bound := fun x ↦ ‖f x‖)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun M ↦
        (hf.norm.aestronglyMeasurable.indicator₀ (hnull M))
    · exact Eventually.of_forall fun M ↦ by
        refine ae_of_all _ fun x ↦ ?_
        rw [norm_indicator_eq_indicator_norm]
        by_cases hmem : x ∈ {x : Fin n → ℝ | M < ‖f x‖}
        · rw [Set.indicator_of_mem hmem]
          simp
        · rw [Set.indicator_of_notMem hmem]
          exact norm_nonneg _
    · exact hf.norm
    · refine ae_of_all _ fun x ↦ ?_
      have hzero : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop] fun M ↦ F M x := by
        show ∀ᶠ M : ℝ in atTop, (0 : ℝ) = F M x
        rw [Filter.eventually_atTop]
        refine ⟨‖f x‖, ?_⟩
        intro M hM
        have hnot : x ∉ {x : Fin n → ℝ | M < ‖f x‖} := by
          exact fun hlt ↦ (not_lt.mpr hM) hlt
        change 0 = ({x : Fin n → ℝ | M < ‖f x‖}.indicator (fun y ↦ ‖f y‖) x)
        rw [Set.indicator_of_notMem hnot]
      exact tendsto_const_nhds.congr' hzero
    )
  convert h_indicator using 1
  funext M
  symm
  exact MeasureTheory.integral_indicator₀ (hnull M)

/-- Bounded function on a small set has small integral. -/
lemma integral_le_bound_mul_measure
    {f : (Fin n → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hfinite : volume E < ⊤)
    (hbound : ∀ x ∈ E, ‖f x‖ ≤ M) :
    ∫ x in E, ‖f x‖ ∂volume ≤ M * (volume E).toReal := by
  by_cases hfi : IntegrableOn (fun x : Fin n → ℝ ↦ ‖f x‖) E volume
  · have hconst : IntegrableOn (fun _ : Fin n → ℝ ↦ M) E volume :=
      integrableOn_const hfinite.ne
    have hle :=
      MeasureTheory.setIntegral_mono_on hfi hconst hE hbound
    rw [MeasureTheory.setIntegral_const] at hle
    simpa [smul_eq_mul, MeasureTheory.measureReal_def, mul_comm] using hle
  · have hzero : ∫ x in E, ‖f x‖ ∂volume = 0 := by
      simpa [IntegrableOn] using (MeasureTheory.integral_undef hfi :
        ∫ x, ‖f x‖ ∂(volume.restrict E) = 0)
    rw [hzero]
    exact mul_nonneg hM ENNReal.toReal_nonneg

end ApmCanaries.Frames.A94J01.Apm_v2_a94J01_1775002964674.Main
