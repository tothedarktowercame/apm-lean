import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt

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

/-- Part (a), as originally stated.

    **SORRY BOUNDARY:** The classical Fresnel value is an improper oscillatory
    integral. The notation below instead denotes Mathlib's Bochner set
    integral. The preceding lemmas prove that its integrand is not integrable,
    that this integral is therefore zero, and that the displayed right-hand
    side is nonzero. Thus this target cannot be discharged without repairing
    the statement to use an improper-integral limit.
-/
theorem fresnel_integral :
    (∫ x in Set.Ioi (0 : ℝ), cexp (Complex.I * (x : ℂ)^2)) =
      (1 + Complex.I) * (√π) / (2 * (√2)) := by
  sorry

end ApmCanaries.A01A10
