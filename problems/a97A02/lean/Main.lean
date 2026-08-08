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
  /- CLOSER HOP 2 BOUNDARY.

  This hop closes the complete continuity conjunct in
  `apm_a97A02_continuousOn_average`.  The proof equips the restricted measure
  with its inherited `NoAtoms` instance, writes each moving `Icc` integral as
  the difference of two `Iic` primitives via
  `intervalIntegral.integral_Iic_sub_Iic`, and composes Mathlib's
  `IntegrableOn.continuousOn_Iic_primitive_Iic` with the affine endpoints.
  Thus the earlier symmetric-difference/kernel-continuity bridge is no longer
  live.

  The sole remaining bridge is the quantitative estimate.  Source inspection
  found the precise ENNReal comparison theorem
  `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`; applied to the moving restricted
  measure at exponents `1` and `p`, it gives the desired factor before
  division.  What remains is the Lean normalization from the Bochner integral
  norm through `eLpNorm f 1`, monotonicity from
  `apm_a97A02_measure_Icc_le`, and conversion of ENNReal `rpow`/`toReal` into
  the frozen real power `(2*h)^(-(1/p.toReal))`.  Searches of
  `LEMMA-INDEX.md`, `ConstructionTargets/`, the solved problem corpus,
  Mathlib's `CompareExp`, `LpNorm`, set-integral, and interval-integral APIs,
  and git history found no compiled lemma performing that full conversion.
  The frozen statement is unchanged.
  -/
  sorry
