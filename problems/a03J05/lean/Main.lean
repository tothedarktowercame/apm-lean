import Mathlib
import ConstructionTargets.Sinc

/-!
# APM a03J05: A cosine integral

## Statement repairs

None.

## Encoding questions

None. The improper integral over `[0, ∞)` is encoded as the Lebesgue set
integral over `Set.Ioi 0`; changing the endpoint does not affect the integral.

## Source note

The bundle has no `informal-solution.md`: `status.json` records that the
harvested file contained the a03J04 proof and was removed. The TeX statement is
therefore the sole intent source for this formal statement.
-/

open Filter MeasureTheory Set
open scoped FourierTransform

noncomputable section

/-- The integrand `cos(xt) / (1 + x²)`. -/

def apm_a03J05_integrand (t x : ℝ) : ℝ :=
  Real.cos (x * t) / (1 + x ^ 2)

/-- The requested identity at frequency zero. -/
lemma apm_a03J05_integral_zero :
    ∫ x in Ioi (0 : ℝ), apm_a03J05_integrand 0 x ∂volume = Real.pi / 2 := by
  simpa [apm_a03J05_integrand] using
    (integral_Ioi_inv_one_add_sq (i := (0 : ℝ)))

/-- The cosine kernel is even in its frequency parameter. -/
lemma apm_a03J05_integrand_neg (t x : ℝ) :
    apm_a03J05_integrand (-t) x = apm_a03J05_integrand t x := by
  simp only [apm_a03J05_integrand, mul_neg]
  rw [Real.cos_neg]

/-- Consequently the entire improper cosine integral is even in frequency. -/
lemma apm_a03J05_integral_neg (t : ℝ) :
    (∫ x in Ioi (0 : ℝ), apm_a03J05_integrand (-t) x ∂volume) =
      ∫ x in Ioi (0 : ℝ), apm_a03J05_integrand t x ∂volume := by
  apply integral_congr_ae
  filter_upwards with x
  exact apm_a03J05_integrand_neg t x

/-- The oscillatory kernel is absolutely integrable, uniformly dominated by
`(1 + x²)⁻¹`. -/
lemma apm_a03J05_integrable (t : ℝ) :
    Integrable (apm_a03J05_integrand t) volume := by
  apply integrable_inv_one_add_sq.mono'
  · apply Continuous.aestronglyMeasurable
    unfold apm_a03J05_integrand
    exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).div
      (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
  · filter_upwards with x
    unfold apm_a03J05_integrand
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < 1 + x ^ 2),
      inv_eq_one_div]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)

/-- The real Fourier kernel of the two-sided exponential.  This is the
Laplace-transform input for a Fourier-inversion proof of the main identity. -/
lemma apm_a03J05_exp_abs_cos_transform (t : ℝ) :
    (∫ x : ℝ, Real.exp (-|x|) * Real.cos (t * x)) = 2 / (1 + t ^ 2) := by
  have heven (x : ℝ) :
      Real.exp (-|x|) * Real.cos (t * x) =
        (fun y : ℝ => Real.exp (-y) * Real.cos (t * y)) |x| := by
    by_cases hx : 0 ≤ x
    · simp [abs_of_nonneg hx]
    · have hx' : x < 0 := lt_of_not_ge hx
      rw [abs_of_neg hx']
      simp only [neg_neg, mul_neg, Real.cos_neg]
  calc
    (∫ x : ℝ, Real.exp (-|x|) * Real.cos (t * x)) =
        ∫ x : ℝ, (fun y : ℝ => Real.exp (-y) * Real.cos (t * y)) |x| := by
          apply integral_congr_ae
          exact ae_of_all _ heven
    _ = 2 * ∫ x in Ioi (0 : ℝ), Real.exp (-x) * Real.cos (t * x) :=
      integral_comp_abs (f := fun y : ℝ => Real.exp (-y) * Real.cos (t * y))
    _ = 2 * (1 / (1 ^ 2 + t ^ 2)) := by
      congr 1
      simpa only [one_mul, neg_mul] using
        (ConstructionTargets.Sinc.integral_exp_neg_mul_cos_Ioi (a := 1) (by positivity) t)
    _ = 2 / (1 + t ^ 2) := by ring

/-- The two-sided exponential used for Fourier inversion is integrable. -/
lemma apm_a03J05_integrable_exp_neg_abs :
    Integrable (fun x : ℝ => Real.exp (-|x|)) volume := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).congr_fun ?_
      measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    simp [abs_of_pos hx']
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := 1) (by norm_num) 0).congr_fun ?_
      measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := hx
    simp [abs_of_nonpos hx']
  rw [← integrableOn_univ]
  simpa only [Iic_union_Ioi] using hneg.union hpos

/-- The imaginary part of the Fourier kernel vanishes by oddness. -/
lemma apm_a03J05_exp_abs_sin_transform (t : ℝ) :
    (∫ x : ℝ, Real.exp (-|x|) * Real.sin (t * x)) = 0 := by
  let g : ℝ → ℝ := fun x => Real.exp (-|x|) * Real.sin (t * x)
  have hg : Integrable g := by
    refine apm_a03J05_integrable_exp_neg_abs.mono' (by fun_prop) ?_
    filter_upwards with x
    dsimp [g]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)
  have hodd (x : ℝ) : g (-x) = -g x := by
    simp [g, abs_neg]
  have hsubst : (∫ x : ℝ, g (-x)) = ∫ x : ℝ, g x :=
    integral_neg_eq_self g volume
  rw [show (fun x => g (-x)) = fun x => -g x by funext x; exact hodd x,
    integral_neg] at hsubst
  linarith

/-- The complex Fourier transform of the two-sided exponential, in Mathlib's
`2π` normalization. -/
lemma apm_a03J05_fourier_exp_neg_abs (w : ℝ) :
    (𝓕 (fun x : ℝ => (Real.exp (-|x|) : ℂ))) w =
      ((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun x =>
    Complex.exp ((↑(-2 * Real.pi * (x * w)) * Complex.I)) * Real.exp (-|x|)
  have hf : Integrable f := by
    refine apm_a03J05_integrable_exp_neg_abs.mono' (by fun_prop) ?_
    filter_upwards with x
    simp [f, Complex.norm_exp]
  rw [Real.fourier_eq']
  rw [show (fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * inner ℝ x w) * Complex.I)) •
        (Real.exp (-|x|) : ℂ)) = f by
    funext x
    have hinner : inner ℝ x w = x * w := by
      change w * x = x * w
      ring
    simp [f, hinner]]
  change (∫ x : ℝ, f x) = _
  apply Complex.ext
  · change (∫ x : ℝ, f x).re = 2 / (1 + (2 * Real.pi * w) ^ 2)
    have hre : (∫ x : ℝ, (f x).re) = (∫ x : ℝ, f x).re := integral_re hf
    rw [← hre]
    simp only [f, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, one_mul,
      Real.exp_zero, Complex.div_re, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow, mul_one]
    rw [show (∫ x : ℝ, Real.cos (-2 * Real.pi * (x * w)) * Real.exp (-|x|)) =
        ∫ x : ℝ, Real.exp (-|x|) * Real.cos ((2 * Real.pi * w) * x) by
      apply integral_congr_ae
      filter_upwards with x
      rw [show -2 * Real.pi * (x * w) = -(2 * Real.pi * w * x) by ring,
        Real.cos_neg]
      ring]
    simpa using apm_a03J05_exp_abs_cos_transform (2 * Real.pi * w)
  · change (∫ x : ℝ, f x).im = 0
    have him : (∫ x : ℝ, (f x).im) = (∫ x : ℝ, f x).im := integral_im hf
    rw [← him]
    simp only [f, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero,
      Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, one_mul, Real.exp_zero, Complex.ofReal_im, mul_one,
      zero_add]
    rw [show (∫ x : ℝ, Real.sin (-2 * Real.pi * (x * w)) * Real.exp (-|x|)) =
        -(∫ x : ℝ, Real.exp (-|x|) * Real.sin ((2 * Real.pi * w) * x)) by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      rw [show -2 * Real.pi * (x * w) = -(2 * Real.pi * w * x) by ring,
        Real.sin_neg]
      ring]
    rw [apm_a03J05_exp_abs_sin_transform]
    simp

/-- The transformed two-sided exponential is integrable, the second analytic
hypothesis needed by Fourier inversion. -/
lemma apm_a03J05_integrable_fourier_exp_neg_abs :
    Integrable (𝓕 (fun x : ℝ => (Real.exp (-|x|) : ℂ))) volume := by
  have hreal : Integrable (fun w : ℝ => 2 / (1 + (2 * Real.pi * w) ^ 2)) := by
    have hscaled := integrable_inv_one_add_sq.comp_mul_left'
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    have hmul := hscaled.const_mul (2 : ℝ)
    convert hmul using 1
  have hcomplex : Integrable
      (fun w : ℝ => ((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hreal
  exact hcomplex.congr (ae_of_all _ fun w => (apm_a03J05_fourier_exp_neg_abs w).symm)

/-! ## Base case: t = 0 gives ∫₀^∞ 1/(1+x²) dx = π/2

   This uses `integral_Ioi_of_hasDerivAt_of_tendsto'` with f = arctan,
   f' = 1/(1+x²), a = 0, m = π/2 (limit of arctan at ∞), f(0) = 0.
   Proof outline (verified in scratch):
   - `Real.hasDerivAt_arctan` gives HasDerivAt arctan (1/(1+x²)) x
   - `Real.tendsto_arctan_atTop.mono_right (nhdsWithin_le_nhds _)`
     gives Tendsto arctan atTop (𝓝 (π/2))
   - `integral_Ioi_of_hasDerivAt_of_tendsto'` yields
     ∫ x in Ioi 0, (1+x²)⁻¹ = π/2 - arctan 0 = π/2
   - Remaining: IntegrableOn (1/(1+x²)) (Ioi 0) volume
     (follows from comparison with 1/x² for x ≥ 1)

   ## General case: ∫₀^∞ cos(xt)/(1+x²) dx = (π/2) e^{-|t|}

   BLOCKER: This is a classic contour integration result. The standard proof:
   1. Extend to the Fourier transform: ∫₋∞^∞ e^{ixt}/(1+x²) dx = π e^{-|t|}
   2. Close the contour in the upper/lower half-plane for t ≷ 0
   3. Compute the residue at z = i (simple pole): Res = e^{-|t|}/(2i)
   4. By residue theorem: ∫ = 2πi · Res = π e^{-|t|}
   5. F(t) = (1/2) · (full integral) = (π/2) e^{-|t|} by even symmetry

   API searched:
   - `Complex.circleIntegral_sub_inv_smul`, `DiffContOnCl.circleIntegral_sub_inv_smul`
     (Cauchy integral formula — available but would need a full contour setup)
   - No residue theorem lemma in Mathlib for this configuration
   - `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform` has Gaussian
     Fourier transform results but not for rational integrands
   - Fourier transform of 1/(1+x²) is not pre-computed in Mathlib

   Alternative approaches considered:
   - ODE method: F(t) = ∫₀^∞ cos(xt)/(1+x²) dx satisfies F - F'' = 0
     (distributionally), with F(0) = π/2, F'(0) = 0.
     BLOCKER: justifying F - F'' = 0 requires differentiating under the integral
     twice, and ∫₀^∞ x²cos(xt)/(1+x²) dx diverges, so this needs regularization.
   - Laplace transform / residue: same contour integration requirement.

   The statement is TRUE as stated; the blocker is Mathlib's lack of contour
   integration / residue calculus infrastructure. -/

theorem apm_a03j05 (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), apm_a03J05_integrand t x ∂volume =
      (Real.pi / 2) * Real.exp (-|t|) := by
  /-
  PARTIAL boundary (closer hop 3).

  `apm_a03J05_integral_zero` now closes the complete `t = 0` case using
  Mathlib's packaged `integral_Ioi_inv_one_add_sq` theorem.

  Beyond the original residue search, I inspected Mathlib's Fourier,
  Laplace, Gaussian, Poisson, Cauchy-integral, improper-integral, and
  parametric-integral sources, `LEMMA-INDEX.md`, all closed artifacts, and
  `ConstructionTargets/`.  `ConstructionTargets.Sinc` supplies
  `integral_exp_neg_mul_cos_Ioi`, which proves the elementary Laplace transform
  `∫ exp (-a*x) cos (t*x) = a/(a²+t²)`.  Using it here would still require a
  new Fubini/Laplace-inversion argument with domination for the oscillatory
  integral.  No corpus theorem packages that inversion, the Fourier transform
  of `1/(1+x²)`, a semicircle-contour limit, or residue calculus.  Sibling
  `a97J06` independently reaches the same boundary for `1/(x²+4)`.

  This hop proves `apm_a03J05_integrand_neg` and
  `apm_a03J05_integral_neg`, completing the evenness reduction that matches
  the right side's `|t|`; only nonnegative frequencies need a transform
  evaluation. Thus the nonzero-frequency evaluation remains open; the ODE route still
  introduces the non-Bochner-integrable term `∫ cos (t*x)`, while the contour
  route requires an ad hoc arc construction and vanishing estimate.

  This final closer hop additionally proves `apm_a03J05_integrable`, by
  dominating the absolute value of the cosine kernel with Mathlib's globally
  integrable `(1 + x^2)⁻¹`. This discharges the basic Bochner-integrability
  obligation needed by either a future Fubini or Fourier-transform route, but
  it does not manufacture the missing transform evaluation. Renewed source
  inspection found `integrable_inv_one_add_sq` and nearby compiled domination
  patterns, but no stronger oscillatory-integral theorem. The remaining bridge
  is still the nonzero-frequency transform evaluation itself.

  F31 opens a different route through Mathlib's Fourier inversion theorem.
  The new compiled lemma `apm_a03J05_exp_abs_cos_transform` evaluates the
  real part of the Fourier transform of `x ↦ exp (-|x|)` on the full line:
  `∫ exp (-|x|) cos (t*x) = 2 / (1+t²)`.  It uses the already compiled
  Laplace-cosine integral from `ConstructionTargets.Sinc` and Mathlib's
  `integral_comp_abs`, so it avoids contour integration entirely.  To finish
  this route one must package the vanishing odd sine part into the complex
  identity for `𝓕 (fun x : ℝ ↦ (Real.exp (-|x|) : ℂ))`, prove that rational
  transform integrable after the `2*π` scaling, apply
  `Integrable.fourierInv_fourier_eq`, and extract/rescale its real part to the
  requested positive-half-line cosine integral.

  F31 round 2 compiles all prerequisites named in the previous residual:
  `apm_a03J05_integrable_exp_neg_abs` supplies the original `L¹` hypothesis;
  `apm_a03J05_exp_abs_sin_transform` proves the odd imaginary part vanishes;
  `apm_a03J05_fourier_exp_neg_abs` packages the exact complex Fourier transform
  in Mathlib's `2*π` normalization; and
  `apm_a03J05_integrable_fourier_exp_neg_abs` supplies the transformed `L¹`
  hypothesis.  What remains is now only the inversion application at `t`, its
  expansion via `Real.fourierInv_eq'`, the positive dilation `x = 2*π*w`, and
  taking real parts/evenness to identify the requested half-line integral.
  -/
  sorry

end
