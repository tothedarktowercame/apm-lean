import Mathlib

/-!
# APM a97A02 — continuity and bounds for sliding averages

## Statement repairs

None.

## Encoding questions

An `L^p([0,1])` function is represented by a measurable representative on
`ℝ` with `MemLp` for Lebesgue measure restricted to `Icc 0 1`. Consequently
the integral over `[t-h,t+h]` automatically uses the zero extension outside
`[0,1]`. The norm is Mathlib's `snorm` of that representative.
-/

open MeasureTheory Set

noncomputable section

def apm_a97A02_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def apm_a97A02_average (f : ℝ → ℂ) (h t : ℝ) : ℂ :=
  (∫ x in Set.Icc (t - h) (t + h), f x ∂apm_a97A02_measure) / (2 * h)

lemma apm_a97A02_integrable_of_memLp
    {p : ENNReal} (hp : 1 ≤ p) {f : ℝ → ℂ}
    (hf : MemLp f p apm_a97A02_measure) :
    Integrable f apm_a97A02_measure := by
  letI : IsFiniteMeasure apm_a97A02_measure := by
    unfold apm_a97A02_measure
    infer_instance
  exact hf.integrable hp

lemma apm_a97A02_measure_Icc_le (h t : ℝ) (_hh : 0 < h) :
    apm_a97A02_measure (Set.Icc (t - h) (t + h)) ≤ ENNReal.ofReal (2 * h) := by
  calc
    apm_a97A02_measure (Set.Icc (t - h) (t + h))
        ≤ volume (Set.Icc (t - h) (t + h)) :=
      Measure.restrict_le_self
        (Set.Icc (t - h) (t + h))
    _ = ENNReal.ofReal (2 * h) := by
      rw [Real.volume_Icc]
      congr 1
      linarith

/-- The moving set integral is continuous.  This uses the atomless primitive
API from `MeasureTheory.Integral.DominatedConvergence`; writing an `Icc`
integral as the difference of two `Iic` primitives avoids any symmetric-
difference bookkeeping. -/
lemma apm_a97A02_continuousOn_average
    (f : ℝ → ℂ) (hf : Integrable f apm_a97A02_measure)
    (h : ℝ) (hh : 0 < h) :
    ContinuousOn (apm_a97A02_average f h) (Set.Icc (0 : ℝ) 1) := by
  letI : NoAtoms apm_a97A02_measure := by
    unfold apm_a97A02_measure
    infer_instance
  let F : ℝ → ℂ := fun b => ∫ x in Set.Iic b, f x ∂apm_a97A02_measure
  have hF : ContinuousOn F (Set.Iic (1 + h)) := by
    exact hf.integrableOn.continuousOn_Iic_primitive_Iic
  have hleft : ContinuousOn (fun t : ℝ => F (t - h)) (Set.Icc (0 : ℝ) 1) := by
    exact hF.comp (continuous_id.sub continuous_const).continuousOn (by
      intro t ht
      simp only [Set.mem_Iic]
      linarith [ht.2])
  have hright : ContinuousOn (fun t : ℝ => F (t + h)) (Set.Icc (0 : ℝ) 1) := by
    exact hF.comp (continuous_id.add continuous_const).continuousOn (by
      intro t ht
      simp only [Set.mem_Iic]
      linarith [ht.2])
  have hnum : ContinuousOn
      (fun t : ℝ => ∫ x in Set.Icc (t - h) (t + h), f x ∂apm_a97A02_measure)
      (Set.Icc (0 : ℝ) 1) := by
    refine (hright.sub hleft).congr fun t ht => ?_
    simp only [F]
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by linarith : t - h ≤ t + h)]
    exact (intervalIntegral.integral_Iic_sub_Iic
      hf.integrableOn hf.integrableOn).symm
  unfold apm_a97A02_average
  exact hnum.div_const (2 * h)

theorem apm_a97a02
    (p : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (f : ℝ → ℂ) (hf : MemLp f p apm_a97A02_measure)
    (h : ℝ) (hh : 0 < h) :
    ContinuousOn (apm_a97A02_average f h) (Set.Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖apm_a97A02_average f h t‖ ≤
        (2 * h) ^ (-(1 / p.toReal)) *
          (eLpNorm f p apm_a97A02_measure).toReal := by
  refine ⟨apm_a97A02_continuousOn_average f
    (apm_a97A02_integrable_of_memLp hp hf) h hh, ?_⟩
  intro t ht
  let E : Set ℝ := Set.Icc (t - h) (t + h)
  let μE := apm_a97A02_measure.restrict E
  have hμE_le : μE ≤ apm_a97A02_measure := Measure.restrict_le_self
  have hmeasE : AEStronglyMeasurable f μE := hf.1.mono_measure hμE_le
  have hp_real : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp_top hp
    norm_num at this ⊢
    exact this
  have hexp : 0 ≤ 1 - 1 / p.toReal := by
    rw [sub_nonneg]
    simpa using one_div_le_one_div_of_le (a := (1 : ℝ)) zero_lt_one hp_real
  have hL1 : eLpNorm f 1 μE ≤
      eLpNorm f p apm_a97A02_measure *
        ENNReal.ofReal (2 * h) ^ (1 - 1 / p.toReal) := by
    calc
      eLpNorm f 1 μE ≤ eLpNorm f p μE *
          μE Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hmeasE
      _ ≤ eLpNorm f p apm_a97A02_measure *
          ENNReal.ofReal (2 * h) ^ (1 - 1 / p.toReal) := by
        have hμ : μE Set.univ ≤ ENNReal.ofReal (2 * h) := by
          simpa [μE, E] using apm_a97A02_measure_Icc_le h t hh
        rw [show 1 / (1 : ENNReal).toReal - 1 / p.toReal =
          1 - 1 / p.toReal by norm_num]
        exact mul_le_mul'
          (eLpNorm_mono_measure f hμE_le)
          (ENNReal.rpow_le_rpow hμ hexp)
  have hnormInt : ‖∫ x, f x ∂μE‖ ≤ (eLpNorm f 1 μE).toReal := by
    simpa [eLpNorm_one_eq_lintegral_enorm] using
      (MeasureTheory.norm_integral_le_lintegral_norm (μ := μE) f)
  have hLp_top : eLpNorm f p apm_a97A02_measure ≠ ⊤ := hf.2.ne
  have hfactor_top : ENNReal.ofReal (2 * h) ^ (1 - 1 / p.toReal) ≠ ⊤ := by
    exact ENNReal.rpow_ne_top_of_nonneg hexp ENNReal.ofReal_ne_top
  have hL1real : (eLpNorm f 1 μE).toReal ≤
      (eLpNorm f p apm_a97A02_measure).toReal *
        (2 * h) ^ (1 - 1 / p.toReal) := by
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hLp_top hfactor_top) hL1
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (by positivity)] at hreal
    exact hreal
  unfold apm_a97A02_average
  rw [show (∫ x in E, f x ∂apm_a97A02_measure) = ∫ x, f x ∂μE by rfl,
    norm_div]
  norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  calc
    ‖∫ x, f x ∂μE‖ / (2 * h) ≤ (eLpNorm f 1 μE).toReal / (2 * h) :=
      div_le_div_of_nonneg_right hnormInt (by positivity)
    _ ≤ ((eLpNorm f p apm_a97A02_measure).toReal *
        (2 * h) ^ (1 - 1 / p.toReal)) / (2 * h) :=
      div_le_div_of_nonneg_right hL1real (by positivity)
    _ = (2 * h) ^ (-p.toReal⁻¹) *
        (eLpNorm f p apm_a97A02_measure).toReal := by
      have hx : 0 < 2 * h := by positivity
      rw [div_eq_mul_inv,
        show (2 * h)⁻¹ = (2 * h) ^ (-1 : ℝ) by
          exact (Real.rpow_neg_one (2 * h)).symm]
      rw [show (eLpNorm f p apm_a97A02_measure).toReal *
          (2 * h) ^ (1 - 1 / p.toReal) * (2 * h) ^ (-1 : ℝ) =
          ((2 * h) ^ (1 - 1 / p.toReal) * (2 * h) ^ (-1 : ℝ)) *
            (eLpNorm f p apm_a97A02_measure).toReal by ring,
        ← Real.rpow_add hx]
      rw [show 1 - 1 / p.toReal + (-1 : ℝ) = -p.toReal⁻¹ by
        rw [one_div]
        ring]
