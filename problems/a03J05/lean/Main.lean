import Mathlib

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
  -/
  sorry

end
