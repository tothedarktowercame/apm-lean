import Mathlib

/-!
# APM a99J09 — holomorphicity of the Laplace transform

## Statement repairs

None.

## Encoding notes

The source function on `[0, ∞)` is represented by an ambient function on `ℝ`
whose `Lᵖ` hypothesis uses `volume.restrict (Set.Ici 0)`.  Its Laplace
transform is likewise integrated over `Set.Ici 0`.
-/

open scoped ENNReal Topology
open Set Filter MeasureTheory Complex

noncomputable def apm_a99j09_laplace (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ici (0 : ℝ), f t * Complex.exp (-(t : ℂ) * z) ∂volume

def apm_a99j09_rightHalfPlane : Set ℂ :=
  {z | 0 < z.re}

/-- Exact norm of the decaying Laplace kernel.  This is the scalar identity
used by the Hölder and local derivative dominators. -/
lemma apm_a99j09_norm_kernel (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-z.re * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
  ring

lemma apm_a99j09_deriv_bound_integrable (f : ℝ → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ici (0 : ℝ))))
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => ‖f t‖ * (t * Real.exp (-a * t)))
      (volume.restrict (Ici (0 : ℝ))) := by
  let q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  letI : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) :=
    hpq.ennrealOfReal
  have hq : 1 < q := hpq.symm.lt
  have hq0 : 0 < q := zero_lt_one.trans hq
  let decay : ℝ → ℝ := fun t => t * Real.exp (-a * t)
  have hdecay_meas :
      AEStronglyMeasurable decay (volume.restrict (Ici (0 : ℝ))) := by
    dsimp [decay]
    fun_prop
  have hdecay_lp :
      MemLp decay (ENNReal.ofReal q) (volume.restrict (Ici (0 : ℝ))) := by
    apply (integrable_norm_rpow_iff hdecay_meas
      (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal hq0.le]
    change Integrable (fun t : ℝ => ‖decay t‖ ^ q)
      (volume.restrict (Ici (0 : ℝ)))
    rw [← IntegrableOn,
      integrableOn_Ici_iff_integrableOn_Ioi (hb := by finiteness)]
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2
    · exact integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := q) (b := a * q) (by linarith) (by norm_num)
          (mul_pos ha hq0)
    intro t ht
    dsimp [decay]
    rw [abs_of_pos (mul_pos ht (Real.exp_pos _))]
    rw [Real.mul_rpow ht.le (Real.exp_pos _).le]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    simp only [Real.rpow_one]
    congr 1
    ring_nf
  have hprod : Integrable (fun t => f t * (decay t : ℂ))
      (volume.restrict (Ici (0 : ℝ))) := hf.integrable_mul hdecay_lp.ofReal
  refine hprod.norm.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  simp only [Complex.norm_mul, Complex.norm_real, decay]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg ht (Real.exp_pos _).le)]

lemma apm_a99j09_integrand_integrable (f : ℝ → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ici (0 : ℝ))))
    {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t => f t * Complex.exp (-(t : ℂ) * z))
      (volume.restrict (Ici (0 : ℝ))) := by
  let q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  letI : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) :=
    hpq.ennrealOfReal
  have hq : 1 < q := hpq.symm.lt
  have hk_meas : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-(t : ℂ) * z))
      (volume.restrict (Ici (0 : ℝ))) := by fun_prop
  have hk_lp : MemLp (fun t : ℝ => Complex.exp (-(t : ℂ) * z))
      (ENNReal.ofReal q) (volume.restrict (Ici (0 : ℝ))) := by
    have hq0 : 0 < q := zero_lt_one.trans hq
    apply (integrable_norm_rpow_iff hk_meas
      (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal hq0.le]
    change Integrable (fun t : ℝ => ‖Complex.exp (-(t : ℂ) * z)‖ ^ q)
      (volume.restrict (Ici (0 : ℝ)))
    rw [← IntegrableOn]
    apply (integrableOn_Ici_iff_integrableOn_Ioi).2
    convert integrableOn_exp_mul_Ioi
      (a := -(z.re * q)) (neg_lt_zero.mpr (mul_pos hz hq0)) 0 using 1
    funext t
    rw [apm_a99j09_norm_kernel, Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp]
    congr 1
    ring
  simpa only [Pi.mul_apply] using hf.integrable_mul hk_lp

theorem apm_a99j09 (f : ℝ → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ici (0 : ℝ)))) :
    DifferentiableOn ℂ (apm_a99j09_laplace f) apm_a99j09_rightHalfPlane := by
  classical
  intro z₀ hz₀
  have hz₀pos : 0 < z₀.re := hz₀
  let r := z₀.re / 2
  have hr : 0 < r := half_pos hz₀pos
  let a := z₀.re / 2
  have ha : 0 < a := half_pos hz₀pos
  let F : ℂ → ℝ → ℂ := fun z t => f t * Complex.exp (-(t : ℂ) * z)
  let F' : ℂ → ℝ → ℂ :=
    fun z t => f t * (-(t : ℂ) * Complex.exp (-(t : ℂ) * z))
  let bound : ℝ → ℝ := fun t => ‖f t‖ * (t * Real.exp (-a * t))
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z)
      (volume.restrict (Ici (0 : ℝ))) := by
    filter_upwards [] with z
    dsimp [F]
    exact hf.aestronglyMeasurable.mul (by fun_prop)
  have hF_int : Integrable (F z₀) (volume.restrict (Ici (0 : ℝ))) := by
    simpa only [F] using apm_a99j09_integrand_integrable f p hp hf hz₀pos
  have hF'_meas : AEStronglyMeasurable (F' z₀)
      (volume.restrict (Ici (0 : ℝ))) := by
    dsimp [F']
    exact hf.aestronglyMeasurable.mul (by fun_prop)
  have hbound_int : Integrable bound (volume.restrict (Ici (0 : ℝ))) := by
    simpa only [bound] using apm_a99j09_deriv_bound_integrable f p hp hf ha
  have hbound : ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∀ z ∈ Metric.ball z₀ r, ‖F' z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht z hz
    change 0 ≤ t at ht
    have hnorm : ‖z - z₀‖ < r := by simpa [dist_eq] using hz
    have habs : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
    have hre : a ≤ z.re := by
      dsimp [a, r] at hnorm ⊢
      change |z.re - z₀.re| ≤ ‖z - z₀‖ at habs
      have hneg : -|(z - z₀).re| ≤ (z - z₀).re := neg_abs_le _
      change -|z.re - z₀.re| ≤ z.re - z₀.re at hneg
      linarith
    have hexp : Real.exp (-z.re * t) ≤ Real.exp (-a * t) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_right (neg_le_neg hre) ht
      simpa [neg_mul] using hm
    dsimp [F', bound]
    rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_of_nonneg ht]
    change ‖f t‖ * (t * ‖Complex.exp (-(t : ℂ) * z)‖) ≤
      ‖f t‖ * (t * Real.exp (-a * t))
    rw [apm_a99j09_norm_kernel]
    gcongr
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∀ z ∈ Metric.ball z₀ r, HasDerivAt (fun z => F z t) (F' z t) z := by
    filter_upwards [] with t z hz
    have hlin : HasDerivAt (fun w : ℂ => -(t : ℂ) * w) (-(t : ℂ)) z := by
      simpa using (hasDerivAt_id z).const_mul (-(t : ℂ))
    have he := (Complex.hasDerivAt_exp (-(t : ℂ) * z)).comp z hlin
    dsimp [F, F']
    convert HasDerivAt.const_mul (f t) he using 1 <;> ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ hr) hF_meas hF_int hF'_meas hbound
      hbound_int hdiff
  have hd : DifferentiableAt ℂ (apm_a99j09_laplace f) z₀ := by
    unfold apm_a99j09_laplace
    simpa only [F] using hmain.2.differentiableAt
  exact hd.differentiableWithinAt
