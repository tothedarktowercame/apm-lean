import Mathlib
import ApmCanaries.Frames.A94A01.Apm_v2_a94A01_1775002871618.Scratch

open MeasureTheory Filter Set
open scoped symmDiff

noncomputable section

namespace ApmCanaries.Frames.A94A01.Apm_v2_a94A01_1775002871618.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

/-- The a.e. pointwise limit of characteristic functions is again a characteristic function a.e. -/
theorem ae_limit_indicator_eq_indicator
    {Eₙ : ℕ → Set ℝ}
    (hm : ∀ n, MeasurableSet (Eₙ n))
    {f : ℝ → ℝ}
    (hlim : ∀ᵐ x ∂volume,
      Tendsto (fun n => (Eₙ n).indicator (fun _ => (1 : ℝ)) x) atTop (nhds (f x))) :
    ∃ E : Set ℝ, MeasurableSet E ∧ f =ᵐ[volume] E.indicator (fun _ => (1 : ℝ)) := by
  have hmeas_ind (n : ℕ) :
      AEMeasurable ((Eₙ n).indicator (fun _ => (1 : ℝ))) volume :=
    (measurable_const.indicator (hm n)).aemeasurable
  have hfmeas : AEMeasurable f volume :=
    aemeasurable_of_tendsto_metrizable_ae' hmeas_ind hlim
  let s : Set ℝ := {x | f x = 1}
  have hs : NullMeasurableSet s volume :=
    hfmeas.nullMeasurableSet_preimage (measurableSet_singleton 1)
  refine ⟨toMeasurable volume s, measurableSet_toMeasurable _ _, ?_⟩
  filter_upwards [hlim, hs.toMeasurable_ae_eq] with x hx hxs
  have hf01 : f x ∈ ({0, 1} : Set ℝ) := by
    apply (isClosed_singleton.union isClosed_singleton).mem_of_tendsto hx
    filter_upwards with n
    by_cases hn : x ∈ Eₙ n <;> simp [hn]
  by_cases hfx : f x = 1
  · rw [Set.indicator_of_mem]
    · exact hfx
    · exact hxs.mpr hfx
  · have hfx0 : f x = 0 := by simpa [Set.mem_insert_iff, hfx] using hf01
    rw [Set.indicator_of_notMem]
    · exact hfx0
    · exact fun hxE ↦ hfx (hxs.mp hxE)

/-- Dominated convergence for integrals over the limiting measurable set. -/
theorem tendsto_setIntegral_of_indicator_limit
    {Eₙ : ℕ → Set ℝ} {E : Set ℝ}
    (hm : ∀ n, MeasurableSet (Eₙ n))
    (hE : MeasurableSet E)
    (hlim : ∀ᵐ x ∂volume,
      Tendsto (fun n => (Eₙ n).indicator (fun _ => (1 : ℝ)) x)
        atTop (nhds (E.indicator (fun _ => (1 : ℝ)) x)))
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    Tendsto (fun n => ∫ x in Eₙ n, g x ∂volume)
      atTop (nhds (∫ x in E, g x ∂volume)) := by
  have hpoint : ∀ᵐ x ∂volume,
      Tendsto (fun n ↦ (Eₙ n).indicator g x) atTop (nhds (E.indicator g x)) := by
    filter_upwards [hlim] with x hx
    have hmul := hx.mul_const (g x)
    convert hmul using 1
    · funext n
      by_cases hn : x ∈ Eₙ n <;> simp [hn]
    · by_cases hxE : x ∈ E <;> simp [hxE]
  have hdc := tendsto_integral_of_dominated_convergence
    (μ := volume) (F := fun n ↦ (Eₙ n).indicator g) (f := E.indicator g)
    (fun x ↦ ‖g x‖)
    (fun n ↦ hg.aestronglyMeasurable.indicator (hm n))
    hg.norm
    (fun n ↦ by
      filter_upwards with x
      by_cases hx : x ∈ Eₙ n <;> simp [hx])
    hpoint
  simpa only [integral_indicator (hm _), integral_indicator hE] using hdc

/-- `Lᵖ` convergence of characteristic functions is equivalent to convergence of the
measure of the symmetric difference. -/
theorem tendsto_eLpNorm_indicator_sub_iff_tendsto_measure_symmDiff
    {Eₙ : ℕ → Set ℝ} {E : Set ℝ}
    (hm : ∀ n, MeasurableSet (Eₙ n))
    (hE : MeasurableSet E)
    {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    Tendsto
        (fun n =>
          eLpNorm
            ((Eₙ n).indicator (fun _ => (1 : ℝ)) - E.indicator (fun _ => (1 : ℝ)))
            p volume)
        atTop (nhds 0) ↔
      Tendsto (fun n => volume (Eₙ n ∆ E)) atTop (nhds 0) := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hsymm (n : ℕ) : MeasurableSet (Eₙ n ∆ E) := (hm n).symmDiff hE
  simp_rw [eLpNorm_indicator_sub_indicator,
    eLpNorm_indicator_const (hsymm _) hp0 hp_top, enorm_one, one_mul]
  constructor
  · intro h
    have hpow := h.ennrpow_const p.toReal
    convert hpow using 1
    · funext n
      rw [← ENNReal.rpow_mul]
      rw [one_div, inv_mul_cancel₀ hpr.ne', ENNReal.rpow_one]
    · exact congrArg nhds (ENNReal.zero_rpow_of_pos hpr).symm
  · intro h
    convert h.ennrpow_const (1 / p.toReal) using 1
    exact congrArg nhds (ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpr)).symm

end ApmCanaries.Frames.A94A01.Apm_v2_a94A01_1775002871618.Main
