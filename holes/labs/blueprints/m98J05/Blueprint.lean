import Mathlib

/-!
# APM m98J05

## Statement repairs

The differentiation rule printed in part (b) omits the hypotheses needed for
integration by parts. It is stated for a differentiable function whose value
and derivative are integrable and whose boundary values vanish at both ends.
For parts (c)--(d), the initial datum is minimally strengthened to `C²`, with
its first two derivatives integrable, so that the displayed classical heat
equation and all Fourier transforms in the statement are defined.

## Encoding questions

The Fourier convention is fixed explicitly with kernel `exp (-i ξ x)`. The
heat equation is expressed by a real derivative in time equalling the second
real derivative in space. The initial condition is the right-hand limit as
`t → 0`, since the convolution formula is defined for `t > 0`.
-/

open Set Filter MeasureTheory intervalIntegral
open scoped Topology FourierTransform

/-- Fourier transform with the convention used in the source solution. -/
noncomputable def apm_m98J05_fourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))

lemma apm_m98J05_fourier_integrable (f : ℝ → ℂ) (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x => f x * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) := by
  have hg : Continuous
      (fun x : ℝ => Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) := by
    fun_prop
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with x
  simp [Complex.norm_exp]

/-- The custom unscaled convention is Mathlib's Fourier transform evaluated at
frequency `ξ / (2π)`. -/
lemma apm_m98J05_fourier_eq_mathlib (f : ℝ → ℂ) (ξ : ℝ) :
    apm_m98J05_fourier f ξ = 𝓕 f (ξ / (2 * Real.pi)) := by
  rw [apm_m98J05_fourier, Real.fourier_eq']
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rw [mul_comm]
  apply congrArg (fun z : ℂ => z * f x)
  apply congrArg Complex.exp
  have hi : inner ℝ x (ξ / (2 * Real.pi)) = x * (ξ / (2 * Real.pi)) := by
    rw [show ξ / (2 * Real.pi) = (ξ / (2 * Real.pi)) • (1 : ℝ) by simp,
      real_inner_smul_right]
    have hix : inner ℝ x (1 : ℝ) = x := by
      rw [real_inner_eq_re_inner, RCLike.inner_apply', conj_trivial, mul_one]
      rfl
    rw [hix]
    simp only [smul_eq_mul, mul_one]
    ring
  rw [hi]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The one-dimensional Gaussian heat kernel. -/
noncomputable def apm_m98J05_heatKernel (t x : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt (Real.pi * t))) * Real.exp (-(x ^ 2) / (4 * t))

lemma apm_m98J05_heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ apm_m98J05_heatKernel t x := by
  unfold apm_m98J05_heatKernel
  positivity

/-- The custom heat kernel has unit mass. -/
lemma apm_m98J05_heatKernel_integral {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, apm_m98J05_heatKernel t x ∂volume = 1 := by
  -- (Sibling: a96A04)
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hgauss :
      ∫ x : ℝ, Real.exp (-(1 / (4 * t)) * x ^ 2) =
        Real.sqrt (4 * Real.pi * t) := by
    have h := integral_gaussian (1 / (4 * t))
    rwa [show Real.pi / (1 / (4 * t)) = 4 * Real.pi * t by field_simp] at h
  rw [show apm_m98J05_heatKernel t = fun x ↦
      (1 / (2 * Real.sqrt (Real.pi * t))) *
        Real.exp (-(1 / (4 * t)) * x ^ 2) by
    funext x
    unfold apm_m98J05_heatKernel
    congr 2
    field_simp]
  rw [MeasureTheory.integral_const_mul, hgauss]
  rw [show Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt (Real.pi * t) by
    rw [show 4 * Real.pi * t = 4 * (Real.pi * t) by ring, Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
    norm_num]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hpt)]

lemma apm_m98J05_heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (apm_m98J05_heatKernel t) volume := by
  by_contra h
  have hone := apm_m98J05_heatKernel_integral ht
  rw [integral_undef h] at hone
  norm_num at hone

/-- Convolution of the initial datum with the heat kernel. -/
noncomputable def apm_m98J05_heatSolution (f : ℝ → ℂ) (x t : ℝ) : ℂ :=
  ∫ y, f y * (apm_m98J05_heatKernel t (x - y) : ℂ)

lemma apm_m98J05_heatSolution_integrable
    {f : ℝ → ℂ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => f y * (apm_m98J05_heatKernel t (x - y) : ℂ)) := by
  let C : ℝ := 1 / (2 * Real.sqrt (Real.pi * t))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => f y * (apm_m98J05_heatKernel t (x - y) : ℂ)) volume := by
    exact hf.aestronglyMeasurable.mul
      ((by unfold apm_m98J05_heatKernel; fun_prop : Continuous fun y : ℝ =>
        (apm_m98J05_heatKernel t (x - y) : ℂ)).aestronglyMeasurable)
  refine (hf.norm.const_mul C).mono' hmeas ?_
  filter_upwards with y
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hk : |apm_m98J05_heatKernel t (x - y)| ≤ C := by
    unfold apm_m98J05_heatKernel
    rw [abs_of_nonneg (mul_nonneg hC (Real.exp_nonneg _))]
    apply mul_le_of_le_one_right hC
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hk (norm_nonneg (f y))

lemma apm_m98J05_heatKernel_fourier {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    apm_m98J05_fourier (fun x => (apm_m98J05_heatKernel t x : ℂ)) ξ =
      Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2) := by
  let b : ℂ := (1 / (4 * t) : ℝ)
  have hb : 0 < b.re := by
    dsimp [b]
    positivity
  have hgauss := fourierIntegral_gaussian hb (-(ξ : ℂ))
  rw [apm_m98J05_fourier]
  have hint :
      (fun x : ℝ => (apm_m98J05_heatKernel t x : ℂ) *
        Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) =
      fun x : ℝ => (1 / (2 * Real.sqrt (Real.pi * t)) : ℂ) *
        (Complex.exp (Complex.I * (-(ξ : ℂ)) * (x : ℂ)) *
          Complex.exp (-b * (x : ℂ) ^ 2)) := by
    funext x
    unfold apm_m98J05_heatKernel
    push_cast
    rw [mul_assoc]
    congr 1
    rw [mul_comm]
    congr 1
    apply congrArg Complex.exp
    dsimp [b]
    push_cast
    field_simp
    apply congrArg Complex.exp
    dsimp [b]
    push_cast
    field_simp
  rw [hint]
  change (∫ x : ℝ, (1 / (2 * Real.sqrt (Real.pi * t)) : ℂ) •
      (Complex.exp (Complex.I * (-(ξ : ℂ)) * (x : ℂ)) *
        Complex.exp (-b * (x : ℂ) ^ 2))) = _
  rw [MeasureTheory.integral_smul, hgauss]
  have hsqrt : (Real.sqrt (4 * Real.pi * t) : ℂ) =
      ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) := by
    rw [show (Real.pi : ℂ) / b = (4 * Real.pi * t : ℝ) by
      dsimp [b]
      push_cast
      field_simp]
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow]
    · norm_num
    · positivity
  rw [← hsqrt]
  push_cast
  rw [show Real.sqrt (4 * Real.pi * t) =
      2 * Real.sqrt (Real.pi * t) by
    rw [show 4 * Real.pi * t = 4 * (Real.pi * t) by ring,
      Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
    norm_num]
  have hroot : Real.sqrt (Real.pi * t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos Real.pi_pos ht))
  have hexp : -(-(ξ : ℂ)) ^ 2 / (4 * b) =
      -(t : ℂ) * (ξ : ℂ) ^ 2 := by
    dsimp [b]
    push_cast
    field_simp
  rw [hexp]
  simp only [smul_eq_mul]
  push_cast
  field_simp [hroot]
  rw [div_self]
  exact_mod_cast hroot

/-- Why this unblocks `apm_m98j05`: the positive unit-mass Gaussians form an
approximate identity, so convolution with continuous `L¹` data converges at
each point as time tends to zero from the right. -/
theorem apm_m98J05_bridge_1
    (f : ℝ → ℂ) (hf_cont : Continuous f) (hf : Integrable f) (x : ℝ) :
    Tendsto (fun t ↦ apm_m98J05_heatSolution f x t)
      (nhdsWithin 0 (Ioi 0)) (nhds (f x)) := by
  sorry

/-- Why this unblocks `apm_m98j05`: domination by derivatives of a positive-
time Gaussian justifies differentiating the convolution in both variables;
the kernel identity `∂ₜG = ∂ₓ²G` then gives the classical heat equation. -/
theorem apm_m98J05_bridge_2
    (f : ℝ → ℂ) (hf : Integrable f) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun s ↦ apm_m98J05_heatSolution f x s)
      (iteratedDeriv 2 (fun z ↦ apm_m98J05_heatSolution f z t) x) t := by
  sorry

lemma apm_m98J05_fourier_convolution_integrable_prod
    (f : ℝ → ℂ) (hf : Integrable f) (ξ t : ℝ) (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ =>
      f p.2 * (apm_m98J05_heatKernel t (p.1 - p.2) : ℂ) *
        Complex.exp (-Complex.I * (ξ : ℂ) * (p.1 : ℂ)))
      (volume.prod volume) := by
  have hk : Integrable (fun x : ℝ =>
      (apm_m98J05_heatKernel t x : ℂ)) :=
    (apm_m98J05_heatKernel_integrable ht).ofReal
  have hbase := hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hk
  refine hbase.norm.mono' ?_ ?_
  · exact hbase.aestronglyMeasurable.mul
      ((by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.exp (-Complex.I * (ξ : ℂ) * (p.1 : ℂ))).aestronglyMeasurable)
  · filter_upwards with p
    simp [Complex.norm_exp]

/-- Why this unblocks `apm_m98j05`: absolute integrability of the two-variable
integrand permits Fubini, and the exactly normalized Gaussian transform turns
the Fourier transform of the convolution into the displayed heat multiplier. -/
theorem apm_m98J05_bridge_3
    (f : ℝ → ℂ) (hf : Integrable f) (ξ t : ℝ) (ht : 0 < t) :
    apm_m98J05_fourier (fun x ↦ apm_m98J05_heatSolution f x t) ξ =
      apm_m98J05_fourier f ξ *
        Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2) := by
  have hprod := apm_m98J05_fourier_convolution_integrable_prod f hf ξ t ht
  rw [apm_m98J05_fourier]
  rw [show (fun x : ℝ => apm_m98J05_heatSolution f x t *
      Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) =
    fun x => ∫ y, f y * (apm_m98J05_heatKernel t (x - y) : ℂ) *
      Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)) by
    funext x
    unfold apm_m98J05_heatSolution
    exact (MeasureTheory.integral_mul_const
      (Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)))
      (fun y => f y * (apm_m98J05_heatKernel t (x - y) : ℂ))).symm]
  rw [MeasureTheory.integral_integral_swap hprod]
  have hinner (y : ℝ) :
      (∫ x : ℝ, f y * (apm_m98J05_heatKernel t (x - y) : ℂ) *
        Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) =
      f y * Complex.exp (-Complex.I * (ξ : ℂ) * (y : ℂ)) *
        Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2) := by
    rw [show (fun x : ℝ => f y * (apm_m98J05_heatKernel t (x - y) : ℂ) *
        Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) =
      fun x => (f y * Complex.exp (-Complex.I * (ξ : ℂ) * (y : ℂ))) *
        ((apm_m98J05_heatKernel t (x - y) : ℂ) *
          Complex.exp (-Complex.I * (ξ : ℂ) * ((x - y : ℝ) : ℂ))) by
      funext x
      have he : Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)) =
          Complex.exp (-Complex.I * (ξ : ℂ) * (y : ℂ)) *
            Complex.exp (-Complex.I * (ξ : ℂ) * ((x - y : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [he]
      ring]
    let C := f y * Complex.exp (-Complex.I * (ξ : ℂ) * (y : ℂ))
    let F := fun x : ℝ => (apm_m98J05_heatKernel t (x - y) : ℂ) *
      Complex.exp (-Complex.I * (ξ : ℂ) * ((x - y : ℝ) : ℂ))
    calc
      (∫ x : ℝ, C * F x) = C * ∫ x : ℝ, F x :=
        MeasureTheory.integral_const_mul C F
      _ = C * apm_m98J05_fourier
          (fun x => (apm_m98J05_heatKernel t x : ℂ)) ξ := by
        congr 1
        dsimp [F]
        rw [apm_m98J05_fourier]
        exact integral_sub_right_eq_self
          (fun x : ℝ => (apm_m98J05_heatKernel t x : ℂ) *
            Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) y (μ := volume)
      _ = C * Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2) := by
        rw [apm_m98J05_heatKernel_fourier ht ξ]
  simp_rw [hinner]
  calc
    (∫ y : ℝ, (f y * Complex.exp (-Complex.I * (ξ : ℂ) * (y : ℂ))) *
      Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2)) =
        (∫ y : ℝ, f y * Complex.exp (-Complex.I * (ξ : ℂ) * (y : ℂ))) *
          Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2) :=
      MeasureTheory.integral_mul_const _ _
    _ = _ := rfl

theorem apm_m98j05 :
    (∀ (f f' : ℝ → ℂ),
      (∀ x, HasDerivAt f (f' x) x) →
      Integrable f → Integrable f' →
      Tendsto f atTop (nhds 0) → Tendsto f atBot (nhds 0) →
      ∀ ξ : ℝ,
        apm_m98J05_fourier f' ξ =
          Complex.I * (ξ : ℂ) * apm_m98J05_fourier f ξ) ∧
    ∀ f : ℝ → ℂ,
      ContDiff ℝ 2 f →
      Integrable f → Integrable (deriv f) → Integrable (iteratedDeriv 2 f) →
      let u := apm_m98J05_heatSolution f
      (∀ x : ℝ,
        Tendsto (fun t ↦ u x t) (nhdsWithin 0 (Ioi 0)) (nhds (f x))) ∧
      (∀ x t : ℝ, 0 < t →
        HasDerivAt (fun s ↦ u x s) (iteratedDeriv 2 (fun z ↦ u z t) x) t) ∧
      (∀ ξ t : ℝ, 0 < t →
        apm_m98J05_fourier (fun x ↦ u x t) ξ =
          apm_m98J05_fourier f ξ * Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2)) ∧
      (∀ ξ t : ℝ, 0 < t →
        HasDerivAt
          (fun s ↦ apm_m98J05_fourier (fun x ↦ u x s) ξ)
          (-((ξ : ℂ) ^ 2) * apm_m98J05_fourier (fun x ↦ u x t) ξ) t) := by
  constructor
  · intro f f' hder hf hf' _ _ ξ
    have hdiff : Differentiable ℝ f := fun x => (hder x).differentiableAt
    have heq : deriv f = f' := by
      funext x
      exact (hder x).deriv
    have hdint : Integrable (deriv f) := by simpa [heq] using hf'
    have hm := congrFun (Real.fourier_deriv hf hdiff hdint) (ξ / (2 * Real.pi))
    rw [apm_m98J05_fourier_eq_mathlib, apm_m98J05_fourier_eq_mathlib]
    rw [heq] at hm
    simp only [smul_eq_mul] at hm
    have hfac : (2 * (Real.pi : ℂ) * Complex.I * (ξ / (2 * Real.pi) : ℝ)) =
        Complex.I * (ξ : ℂ) := by
      push_cast
      field_simp [Real.pi_ne_zero]
    calc
      𝓕 f' (ξ / (2 * Real.pi)) =
          (2 * (Real.pi : ℂ) * Complex.I * (ξ / (2 * Real.pi) : ℝ)) *
            𝓕 f (ξ / (2 * Real.pi)) := hm
      _ = Complex.I * (ξ : ℂ) * 𝓕 f (ξ / (2 * Real.pi)) := by rw [hfac]
  · intro f hf2 hf hf' hf''
    have hmultiplier_ode (c : ℂ) (ξ t : ℝ) :
      HasDerivAt
        (fun s : ℝ ↦ c * Complex.exp (-(s : ℂ) * (ξ : ℂ) ^ 2))
        (-((ξ : ℂ) ^ 2) *
          (c * Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2))) t := by
      have hc : HasDerivAt
          (fun s : ℂ ↦ c * Complex.exp (-s * (ξ : ℂ) ^ 2))
          (-((ξ : ℂ) ^ 2) *
            (c * Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2))) (t : ℂ) := by
        have hg : HasDerivAt (fun s : ℂ ↦ -s * (ξ : ℂ) ^ 2)
            (-((ξ : ℂ) ^ 2)) (t : ℂ) := by
          convert (hasDerivAt_id (x := (t : ℂ))).neg.mul_const ((ξ : ℂ) ^ 2) using 1 <;>
            ring
        convert ((Complex.hasDerivAt_exp _).comp (t : ℂ) hg).const_mul c using 1 <;>
          ring
      exact hc.comp_ofReal
    dsimp
    refine ⟨fun x => apm_m98J05_bridge_1 f hf2.continuous hf x,
      fun x t ht => apm_m98J05_bridge_2 f hf x t ht,
      fun ξ t ht => apm_m98J05_bridge_3 f hf ξ t ht, ?_⟩
    intro ξ t ht
    have heq : (fun s => apm_m98J05_fourier
        (fun x => apm_m98J05_heatSolution f x s) ξ) =ᶠ[𝓝 t]
        (fun s => apm_m98J05_fourier f ξ *
          Complex.exp (-(s : ℂ) * (ξ : ℂ) ^ 2)) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact apm_m98J05_bridge_3 f hf ξ s hs
    have hder :=
      (hmultiplier_ode (apm_m98J05_fourier f ξ) ξ t).congr_of_eventuallyEq heq
    rw [apm_m98J05_bridge_3 f hf ξ t ht]
    exact hder


#print axioms apm_m98j05
