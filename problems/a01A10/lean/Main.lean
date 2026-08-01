import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# APM a01A10: Contour integral computation

**Problem.** Use a contour integral to compute the value of one of:
(a) ∫₀^∞ e^{ix²} dx
(b) ∫_{-∞}^∞ e^{ixy} e^{-x²} dx

**Statement repair note.**

The informal-solution file `apm-a01A10.md` was harvested with the **wrong
content**: it contains the proof for a01A09 (Laplace transform analyticity),
not a01A10 (contour integral). This file implements the correct problem from
`a01A10.tex`.

We compute part (b): the Fourier transform of a Gaussian.

**Answer to (b):** ∫_{-∞}^∞ e^{ixy} e^{-x²} dx = √π · e^{-y²/4}.

**Proof (completing the square + contour shift).**

Write -x² + ixy = -(x - iy/2)² - y²/4. So:
∫ e^{ixy} e^{-x²} dx = e^{-y²/4} ∫ e^{-(x-iy/2)²} dx = e^{-y²/4} √π.

The contour shift (shifting the real line to the line Im(z) = y/2) is
justified by Cauchy's theorem applied to the rectangle with vertices
±R and ±R - iy/2, using that e^{-z²} → 0 on the vertical segments.

**Formalization approach.** We use Mathlib's `integral_gaussian`:
∫ x, exp(-b*x²) = √(π/b). For part (b), we complete the square and apply
a contour-shift argument. The key identity is that
∫ exp(-(x - iy/2)²) dx = ∫ exp(-x²) dx = √π, which requires a contour shift.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Real MeasureTheory
open scoped Topology

namespace ApmCanaries.A01A10

/-- Part (b): The Fourier transform of a Gaussian.
    ∫_{-∞}^∞ e^{ixy} e^{-x²} dx = √π · e^{-y²/4}.

    **SORRY BOUNDARY:** The proof requires a contour-shift argument (shifting
    the contour from ℝ to the line ℂ ∋ z = x - iy/2). While Mathlib has
    `integral_gaussian` (∫ exp(-x²) = √π) and the complex Gaussian
    (`integral_gaussian_sq_complex`), the contour shift is not directly
    available as a Mathlib lemma. The result can also be obtained by
    expanding e^{ixy} = cos(xy) + i·sin(xy) and using the fact that the
    imaginary part (sin, odd) integrates to zero while the real part
    (cos · e^{-x²}) gives √π · e^{-y²/4} via a known identity.
-/
theorem gaussian_fourier_transform (y : ℝ) :
    ∫ x : ℝ, cexp ((Complex.I * ↑y * ↑x) + (-(↑x : ℂ)^2)) = ↑(√π) * cexp (-(↑y : ℂ)^2 / 4) := by
  have h := fourierIntegral_gaussian (b := (1 : ℂ)) (by norm_num) (y : ℂ)
  calc
    (∫ x : ℝ, cexp ((Complex.I * ↑y * ↑x) + (-(↑x : ℂ)^2))) =
        ∫ x : ℝ, cexp (Complex.I * (y : ℂ) * x) *
          cexp (-(1 : ℂ) * x ^ 2) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [← Complex.exp_add]
            congr 1
            ring
    _ = ((π : ℂ) / 1) ^ (1 / 2 : ℂ) *
        cexp (-(y : ℂ) ^ 2 / (4 * 1)) := h
    _ = (√π : ℂ) * cexp (-(y : ℂ)^2 / 4) := by
      rw [div_one]
      have hsqrt : (√π : ℂ) = (π : ℂ) ^ (1 / 2 : ℂ) := by
        rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
        norm_num
      rw [← hsqrt]
      congr 2
      ring

/-- Part (b) via completion of the square:
    -x² + ixy = -(x - iy/2)² - y²/4. -/
lemma complete_square (x y : ℝ) :
    -(x : ℂ)^2 + (Complex.I * (y : ℂ) * x) =
      -(((x : ℂ) - Complex.I * (y : ℂ) / 2)^2) - (y : ℂ)^2 / 4 := by
  -- Verified: expand (x - Iy/2)² = x² - Ixy + I²y²/4 = x² - Ixy - y²/4
  -- Then -(x-Iy/2)² - y²/4 = -x² + Ixy + y²/4 - y²/4 = -x² + Ixy ✓
  ring_nf
  simp [Complex.I_sq]

/-- The displayed Fresnel integrand is not Bochner integrable on the positive
half-line: its norm is identically one there. -/
lemma fresnel_integrand_not_integrable :
    ¬ IntegrableOn (fun x : ℝ => cexp (Complex.I * (x : ℂ)^2)) (Set.Ioi 0) := by
  intro h
  have hnorm (x : ℝ) :
      ‖cexp (Complex.I * (x : ℂ)^2)‖ = (1 : ℝ) := by
    rw [← Complex.ofReal_pow]
    exact Complex.norm_exp_I_mul_ofReal _
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) := by
    exact h.norm.congr (Filter.Eventually.of_forall hnorm)
  have hnot : ¬ IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) := by
    simp [integrableOn_const_iff, volume_Ioi]
  exact hnot hone

/-- Consequently Mathlib's Bochner integral assigns zero to the Fresnel
integrand on the half-line. -/
lemma fresnel_bochner_integral_eq_zero :
    (∫ x in Set.Ioi (0 : ℝ), cexp (Complex.I * (x : ℂ)^2)) = 0 :=
  integral_undef fresnel_integrand_not_integrable

lemma fresnel_claimed_value_ne_zero :
    (1 + Complex.I) * (√π) / (2 * (√2)) ≠ 0 := by
  apply div_ne_zero
  · apply mul_ne_zero
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  · exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'

/-- The stated Fresnel equality is false for the Bochner/set-integral notation
used below; the classical value is instead an improper oscillatory integral. -/
lemma not_fresnel_integral_statement :
    ¬ ((∫ x in Set.Ioi (0 : ℝ), cexp (Complex.I * (x : ℂ)^2)) =
      (1 + Complex.I) * (√π) / (2 * (√2))) := by
  rw [fresnel_bochner_integral_eq_zero]
  exact fresnel_claimed_value_ne_zero.symm

/-- Integration by parts for the Abel-regularized Fresnel tail.  This is the
identity from which one obtains a tail bound uniform in `ε ≥ 0`. -/
lemma damped_fresnel_integration_by_parts
    {ε a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)) =
      (-2 * ((ε : ℂ) - I) * b)⁻¹ * cexp (-((ε : ℂ) - I) * (b : ℂ) ^ 2) -
        (-2 * ((ε : ℂ) - I) * a)⁻¹ * cexp (-((ε : ℂ) - I) * (a : ℂ) ^ 2) -
        ∫ x in a..b,
          (2 * ((ε : ℂ) - I) /
            (-2 * ((ε : ℂ) - I) * (x : ℂ)) ^ 2) *
            cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2) := by
  let q : ℂ := (ε : ℂ) - I
  have hq : q ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [q] at him
  have hx (x : ℝ) (hx : x ∈ Set.uIcc a b) : x ≠ 0 := by
    rw [Set.uIcc_of_le hab] at hx
    exact ne_of_gt (ha.trans_le hx.1)
  have hu (x : ℝ) (hmem : x ∈ Set.uIcc a b) :
      HasDerivAt (fun y : ℝ => (-2 * q * (y : ℂ))⁻¹)
        (2 * q / (-2 * q * (x : ℂ)) ^ 2) x := by
    convert
      ((hasDerivAt_inv (hx x hmem)).ofReal_comp.const_mul (-2 * q)⁻¹) using 1
    · ext y
      simp only [ofReal_inv]
      ring
    · simp
      field_simp
  have hv (x : ℝ) (_hx : x ∈ Set.uIcc a b) :
      HasDerivAt (fun y : ℝ => cexp (-q * (y : ℂ) ^ 2))
        ((-2 * q * (x : ℂ)) * cexp (-q * (x : ℂ) ^ 2)) x := by
    convert
      ((Complex.ofRealCLM.hasDerivAt (x := x).pow 2).const_mul (-q)).cexp using 1
      <;> simp [Complex.ofRealCLM_apply] <;> ring
  have hiu :
      IntervalIntegrable
        (fun x : ℝ => 2 * q / (-2 * q * (x : ℂ)) ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable <| by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hmem
      exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num) hq)
        (ofReal_ne_zero.mpr (hx x hmem)))
  have hiv :
      IntervalIntegrable
        (fun x : ℝ => (-2 * q * (x : ℂ)) * cexp (-q * (x : ℂ) ^ 2)) volume a b :=
    (by fun_prop : Continuous fun x : ℝ =>
      (-2 * q * (x : ℂ)) * cexp (-q * (x : ℂ) ^ 2)).intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hiu hiv
  rw [show (∫ x in a..b, cexp (-q * (x : ℂ) ^ 2)) =
      ∫ x in a..b, (-2 * q * (x : ℂ))⁻¹ *
        ((-2 * q * (x : ℂ)) * cexp (-q * (x : ℂ) ^ 2)) by
    apply intervalIntegral.integral_congr
    intro x hmem
    change cexp (-q * (x : ℂ) ^ 2) =
      (-2 * q * (x : ℂ))⁻¹ * ((-2 * q * (x : ℂ)) * cexp (-q * (x : ℂ) ^ 2))
    have hn : -2 * q * (x : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hq) (ofReal_ne_zero.mpr (hx x hmem))
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]]
  dsimp [q] at hparts ⊢
  exact hparts

/-- The elementary real integral used to bound the remainder in Fresnel
integration by parts. -/
lemma integral_inv_sq_half {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 / (2 * x ^ 2)) = 1 / (2 * a) - 1 / (2 * b) := by
  have hx (x : ℝ) (hmem : x ∈ Set.uIcc a b) : x ≠ 0 := by
    rw [Set.uIcc_of_le hab] at hmem
    exact ne_of_gt (ha.trans_le hmem.1)
  have hd (x : ℝ) (hmem : x ∈ Set.uIcc a b) :
      HasDerivAt (fun y : ℝ => -(1 / 2) * y⁻¹) (1 / (2 * x ^ 2)) x := by
    convert (hasDerivAt_inv (hx x hmem)).const_mul (-(1 / 2 : ℝ)) using 1 <;>
      field_simp
  have hi : IntervalIntegrable (fun x : ℝ => 1 / (2 * x ^ 2)) volume a b :=
    ContinuousOn.intervalIntegrable <| by
      apply ContinuousOn.div continuousOn_const
        (continuousOn_const.mul (continuousOn_id.pow 2))
      intro x hmem
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (hx x hmem))
  have hb : b ≠ 0 := ne_of_gt (ha.trans_le hab)
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi using 1 <;>
    field_simp <;> ring

/-- At zero damping, the integration-by-parts remainder has the elementary
`1 / (2x²)` norm used in the uniform Fresnel tail estimate. -/
lemma fresnel_remainder_norm_eq {x : ℝ} (hx : 0 < x) :
    ‖(2 * ((0 : ℂ) - I) /
        (-2 * ((0 : ℂ) - I) * (x : ℂ)) ^ 2) *
        cexp (-((0 : ℂ) - I) * (x : ℂ) ^ 2)‖ = 1 / (2 * x ^ 2) := by
  rw [norm_mul, norm_div, norm_pow, Complex.norm_exp]
  simp only [zero_sub]
  have hre : (- -I * (x : ℂ) ^ 2).re = 0 := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero, mul_one]
  simp only [norm_mul, norm_neg, Complex.norm_ofNat, norm_I, norm_real]
  rw [Real.norm_eq_abs, abs_of_pos hx]
  field_simp

/-- The complex damping parameter `ε - i` stays uniformly away from zero for
nonnegative damping. -/
lemma one_le_norm_damping {ε : ℝ} (hε : 0 ≤ ε) :
    (1 : ℝ) ≤ ‖(ε : ℂ) - I‖ := by
  rw [← (sq_le_sq₀ zero_le_one (norm_nonneg ((ε : ℂ) - I)))]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith

/-- Abel damping never increases the modulus of the Fresnel integrand. -/
lemma norm_damped_fresnel_le_one {ε x : ℝ} (hε : 0 ≤ ε) :
    ‖cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  simp [pow_two, Complex.mul_re, Complex.mul_im]
  nlinarith [sq_nonneg x]

/-- Uniform estimate for the boundary term in damped Fresnel integration by
parts. -/
lemma damped_fresnel_boundary_norm_le {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) :
    ‖(-2 * ((ε : ℂ) - I) * x)⁻¹ *
        cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1 / (2 * x) := by
  have hq := one_le_norm_damping hε
  have hexp := norm_damped_fresnel_le_one (x := x) hε
  rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  calc
    (2 * ‖(ε : ℂ) - I‖ * x)⁻¹ *
        ‖cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖
      ≤ (2 * ‖(ε : ℂ) - I‖ * x)⁻¹ * 1 := by gcongr
    _ ≤ (2 * 1 * x)⁻¹ * 1 := by gcongr
    _ = 1 / (2 * x) := by ring

/-- Uniform estimate for the remainder term in damped Fresnel integration by
parts. -/
lemma damped_fresnel_remainder_norm_le {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) :
    ‖(2 * ((ε : ℂ) - I) /
        (-2 * ((ε : ℂ) - I) * (x : ℂ)) ^ 2) *
        cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1 / (2 * x ^ 2) := by
  have hq := one_le_norm_damping hε
  have hqpos : 0 < ‖(ε : ℂ) - I‖ := zero_lt_one.trans_le hq
  have hexp := norm_damped_fresnel_le_one (x := x) hε
  rw [norm_mul, norm_div, norm_pow, norm_mul, norm_mul]
  have hnormneg : ‖(-2 : ℂ) * ((ε : ℂ) - I)‖ = 2 * ‖(ε : ℂ) - I‖ := by
    rw [norm_mul]
    norm_num
  rw [hnormneg]
  simp only [Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx]
  calc
    2 * ‖(ε : ℂ) - I‖ / (2 * ‖(ε : ℂ) - I‖ * x) ^ 2 *
        ‖cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖
      ≤ 2 * ‖(ε : ℂ) - I‖ / (2 * ‖(ε : ℂ) - I‖ * x) ^ 2 * 1 := by gcongr
    _ = 1 / (2 * ‖(ε : ℂ) - I‖ * x ^ 2) := by field_simp
    _ ≤ 1 / (2 * 1 * x ^ 2) := by gcongr
    _ = 1 / (2 * x ^ 2) := by ring

/-- The integration-by-parts tail estimate is uniform all the way down to
zero damping. -/
lemma norm_integral_damped_fresnel_le_inv
    {ε a b : ℝ} (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1 / a := by
  let boundary : ℝ → ℂ := fun x =>
    (-2 * ((ε : ℂ) - I) * x)⁻¹ *
      cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)
  let remainder : ℝ → ℂ := fun x =>
    (2 * ((ε : ℂ) - I) /
      (-2 * ((ε : ℂ) - I) * (x : ℂ)) ^ 2) *
      cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)
  have hparts := damped_fresnel_integration_by_parts
    (ε := ε) (a := a) (b := b) ha hab
  have hremnorm :
      ‖∫ x in a..b, remainder x‖ ≤ ∫ x in a..b, 1 / (2 * x ^ 2) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · filter_upwards with x
      intro hx
      rw [Set.mem_Ioc] at hx
      exact damped_fresnel_remainder_norm_le hε (ha.trans hx.1)
    · exact ContinuousOn.intervalIntegrable <| by
        apply ContinuousOn.div continuousOn_const
          (continuousOn_const.mul (continuousOn_id.pow 2))
        intro x hx
        rw [Set.uIcc_of_le hab] at hx
        exact mul_ne_zero (by norm_num)
          (pow_ne_zero 2 (ne_of_gt (ha.trans_le hx.1)))
  have hb : 0 < b := ha.trans_le hab
  have hparts' :
      (∫ x in a..b, cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)) =
        boundary b - boundary a - ∫ x in a..b, remainder x := by
    simpa [boundary, remainder] using hparts
  rw [hparts']
  calc
    ‖boundary b - boundary a - ∫ x in a..b, remainder x‖
        ≤ ‖boundary b‖ + ‖boundary a‖ + ‖∫ x in a..b, remainder x‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 1 / (2 * b) + 1 / (2 * a) +
          (1 / (2 * a) - 1 / (2 * b)) := by
      gcongr
      · exact damped_fresnel_boundary_norm_le hε hb
      · exact damped_fresnel_boundary_norm_le hε ha
      · exact hremnorm.trans_eq (integral_inv_sq_half ha hab)
    _ = 1 / a := by ring

/-- Uniform Abel-regularized tail estimate on the whole positive half-line. -/
lemma norm_integral_Ioi_damped_fresnel_le_inv
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ‖∫ x in Set.Ioi a, cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1 / a := by
  have hb : 0 < (((ε : ℂ) - I).re) := by simpa
  have htend := intervalIntegral_tendsto_integral_Ioi a
    (integrable_cexp_neg_mul_sq hb).integrableOn Filter.tendsto_id
  have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ 1 / a} :=
    isClosed_le continuous_norm continuous_const
  apply hclosed.mem_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop a] with b hab
  exact norm_integral_damped_fresnel_le_inv hε.le ha hab

/-- On every fixed bounded interval, Abel damping can be removed by dominated
convergence. -/
lemma tendsto_integral_damped_fresnel_interval (a : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x in (0 : ℝ)..a,
        cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2))
      (𝓝[>] (0 : ℝ))
      (nhds (∫ x in (0 : ℝ)..a, cexp (I * (x : ℂ) ^ 2))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => 1)
  · filter_upwards with ε
    exact (by fun_prop : Continuous fun x : ℝ =>
      cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards with x
    intro _hx
    exact norm_damped_fresnel_le_one hε.le
  · exact intervalIntegrable_const
  · filter_upwards with x
    intro _hx
    have hc : Filter.Tendsto
        (fun ε : ℝ => cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2))
        (nhds 0) (nhds (cexp (-((0 : ℂ) - I) * (x : ℂ) ^ 2))) :=
      (by fun_prop : Continuous fun ε : ℝ =>
        cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)).tendsto 0
    simpa using hc.mono_left inf_le_left

/-- The undamped Fresnel tails are uniformly Cauchy.  This is the quantitative
Dirichlet estimate used both to construct the improper integral and to remove
Abel damping. -/
lemma norm_integral_fresnel_le_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, cexp (Complex.I * (x : ℂ) ^ 2)‖ ≤ 1 / a := by
  let boundary : ℝ → ℂ := fun x =>
    (-2 * ((0 : ℂ) - I) * x)⁻¹ * cexp (-((0 : ℂ) - I) * (x : ℂ) ^ 2)
  let remainder : ℝ → ℂ := fun x =>
    (2 * ((0 : ℂ) - I) /
      (-2 * ((0 : ℂ) - I) * (x : ℂ)) ^ 2) *
      cexp (-((0 : ℂ) - I) * (x : ℂ) ^ 2)
  have hparts := damped_fresnel_integration_by_parts
    (ε := 0) (a := a) (b := b) ha hab
  have hboundary (x : ℝ) (hx : 0 < x) : ‖boundary x‖ = 1 / (2 * x) := by
    dsimp [boundary]
    rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_neg,
      Complex.norm_ofNat]
    simp only [zero_sub, norm_neg, norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx]
    rw [Complex.norm_exp]
    have hre : (- -I * (x : ℂ) ^ 2).re = 0 := by
      simp [pow_two, Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero, mul_one]
    field_simp
  have hremnorm :
      ‖∫ x in a..b, remainder x‖ ≤
        ∫ x in a..b, 1 / (2 * x ^ 2) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · filter_upwards with x
      intro hx
      rw [Set.mem_Ioc] at hx
      dsimp [remainder]
      exact le_of_eq (fresnel_remainder_norm_eq (ha.trans hx.1))
    · exact ContinuousOn.intervalIntegrable <| by
        apply ContinuousOn.div continuousOn_const
          (continuousOn_const.mul (continuousOn_id.pow 2))
        intro x hx
        rw [Set.uIcc_of_le hab] at hx
        exact mul_ne_zero (by norm_num)
          (pow_ne_zero 2 (ne_of_gt (ha.trans_le hx.1)))
  have hb : 0 < b := ha.trans_le hab
  have hparts' :
      (∫ x in a..b, cexp (I * (x : ℂ) ^ 2)) =
        boundary b - boundary a - ∫ x in a..b, remainder x := by
    simpa [boundary, remainder] using hparts
  rw [hparts']
  calc
    ‖boundary b - boundary a - ∫ x in a..b, remainder x‖
        ≤ ‖boundary b‖ + ‖boundary a‖ +
            ‖∫ x in a..b, remainder x‖ := by
          exact (norm_sub_le _ _).trans
            (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 1 / (2 * b) + 1 / (2 * a) +
          (1 / (2 * a) - 1 / (2 * b)) := by
      gcongr
      · exact (hboundary b hb).le
      · exact (hboundary a ha).le
      · exact hremnorm.trans_eq (integral_inv_sq_half ha hab)
    _ = 1 / a := by ring

/-- The positive Fresnel interval integrals have an improper limit, before its
value is identified by Abel regularization. -/
lemma exists_tendsto_integral_fresnel :
    ∃ L : ℂ, Filter.Tendsto
      (fun R : ℝ => ∫ x in (0 : ℝ)..R, cexp (I * (x : ℂ) ^ 2))
      Filter.atTop (nhds L) := by
  let F : ℝ → ℂ := fun R => ∫ x in (0 : ℝ)..R, cexp (I * (x : ℂ) ^ 2)
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨by infer_instance, ?_⟩
  intro ε hε
  let A : ℝ := max 1 (2 / ε)
  refine ⟨F '' Set.Ici A, ?_, ?_⟩
  · rw [Filter.mem_map]
    exact Filter.mem_of_superset (Filter.Ici_mem_atTop A) fun R hR =>
      ⟨R, hR, rfl⟩
  · have htail {x y : ℝ} (hx : A ≤ x) (hxy : x ≤ y) :
        dist (F x) (F y) < ε := by
      have hA1 : 1 ≤ A := le_max_left _ _
      have hxpos : 0 < x := zero_lt_one.trans_le (hA1.trans hx)
      have h0x : IntervalIntegrable
          (fun z : ℝ => cexp (I * (z : ℂ) ^ 2)) volume 0 x :=
        (by fun_prop : Continuous fun z : ℝ => cexp (I * (z : ℂ) ^ 2))
          |>.intervalIntegrable 0 x
      have hxyint : IntervalIntegrable
          (fun z : ℝ => cexp (I * (z : ℂ) ^ 2)) volume x y :=
        (by fun_prop : Continuous fun z : ℝ => cexp (I * (z : ℂ) ^ 2))
          |>.intervalIntegrable x y
      have hadd := intervalIntegral.integral_add_adjacent_intervals h0x hxyint
      have hdiff : F y - F x =
          ∫ z in x..y, cexp (I * (z : ℂ) ^ 2) := by
        dsimp [F]
        rw [← hadd]
        abel
      have hxA : 2 / ε ≤ x := (le_max_right 1 (2 / ε)).trans hx
      have h2 : 0 < 2 / ε := div_pos (by norm_num) hε
      calc
        dist (F x) (F y) = ‖F y - F x‖ := by
          rw [Complex.dist_eq, norm_sub_rev]
        _ = ‖∫ z in x..y, cexp (I * (z : ℂ) ^ 2)‖ := congrArg norm hdiff
        _ ≤ 1 / x := norm_integral_fresnel_le_inv hxpos hxy
        _ ≤ 1 / (2 / ε) :=
          div_le_div_of_nonneg_left (by norm_num) h2 hxA
        _ = ε / 2 := by field_simp
        _ < ε := half_lt_self hε
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases le_total x y with hxy | hyx
    · exact htail hx hxy
    · simpa [dist_comm] using htail hy hyx

/-- Part (a), stated as the classical improper oscillatory integral.

    **SORRY BOUNDARY:** Proving this limit requires the contour-rotation
    argument described in the informal solution. The preceding lemmas explain
    why it cannot instead be represented by a Bochner integral on `Ioi 0`.
-/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): express the conditionally
-- convergent Fresnel integral as a limit of integrals over bounded intervals.
theorem fresnel_integral :
    Filter.Tendsto
      (fun R : ℝ => ∫ x in (0 : ℝ)..R, cexp (Complex.I * (x : ℂ)^2))
      Filter.atTop
      (nhds ((1 + Complex.I) * (√π) / (2 * (√2)))) := by
  /-
  The uniform finite and half-line tail estimates are now proved in
  `norm_integral_damped_fresnel_le_inv` and
  `norm_integral_Ioi_damped_fresnel_le_inv`; removal of damping on `[0,a]`
  is `tendsto_integral_damped_fresnel_interval`.

  What remains is the final three-ε assembly: split both the regularized
  half-line integral and the improper integral at a common large `a`, use
  those three lemmas on the two tails and the head, and identify the limit of
  `(π / ((ε : ℂ) - I)) ^ (1 / 2 : ℂ) / 2` from
  `integral_gaussian_complex_Ioi`.  The last normalization uses
  `Complex.log_I`, `Real.cos_pi_div_four`, and `Real.sin_pi_div_four` to show
  the principal square root of `π * I` is `(1 + I) * √π / √2`.
  -/
  sorry

end ApmCanaries.A01A10
