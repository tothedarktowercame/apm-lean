/-
! # APM a96A05: 1/z cannot be uniformly approximated by polynomials on the unit circle

For any polynomial `P ∈ ℂ[z]`, `sup_{|z|=1} |1/z - P(z)| ≥ 1`.

## Proof

Use the contour integral. The integral of `1/z` around the unit circle is `2πi`
(winding number 1), while the integral of any polynomial is `0` (Cauchy's theorem).
So `∮ (1/z - P(z)) dz = 2πi`, and `|2πi| = 2π`.

The ML inequality bounds `|∮ f dz| ≤ 2π · sup|f|` on the unit circle.
Combining: `2π ≤ 2π · sup`, hence `sup ≥ 1`.

## Mathlib cross-references

- `circleIntegral.integral_sub_inv_of_mem_ball`: `∮ (z-w)⁻¹ = 2πI` for `w ∈ ball c R`
- `circleIntegral.norm_integral_le_of_norm_le_const`: ML inequality
- `DiffContOnCl.circleIntegral_eq_zero`: Cauchy's theorem
- `circleIntegral.integral_sub`: linearity of the contour integral
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Complex Metric

noncomputable section

/-- The contour integral of `1/z` over the unit circle is `2πi`. -/
lemma circleIntegral_inv :
    ∮ (z : ℂ) in C(0, 1), z⁻¹ = 2 * Real.pi * I := by
  have := circleIntegral.integral_sub_inv_of_mem_ball (w := 0) (R := 1) (c := 0)
    (show (0 : ℂ) ∈ ball (0 : ℂ) 1 from mem_ball.mpr (by simp [dist_self]))
  simpa using this

/-- The contour integral of any polynomial over the unit circle is `0` (Cauchy's theorem). -/
lemma circleIntegral_polynomial (P : Polynomial ℂ) :
    ∮ (z : ℂ) in C(0, 1), Polynomial.aeval z P = 0 := by
  apply DiffContOnCl.circleIntegral_eq_zero (by norm_num : (0:ℝ) ≤ 1)
  exact (P.differentiable_aeval).diffContOnCl

/-- The contour integral of `(1/z - P(z))` over the unit circle equals `2πi`. -/
lemma circleIntegral_inv_sub_polynomial (P : Polynomial ℂ) :
    ∮ (z : ℂ) in C(0, 1), (fun z => z⁻¹ - Polynomial.aeval z P) z = 2 * Real.pi * I := by
  rw [circleIntegral.integral_sub]
  · rw [circleIntegral_inv, circleIntegral_polynomial]; ring
  · apply ContinuousOn.circleIntegrable (by norm_num)
    apply ContinuousOn.inv₀ continuous_id.continuousOn
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    show id z ≠ 0
    intro heq
    rw [show id z = z from rfl] at heq
    rw [heq, norm_zero] at hz
    norm_num at hz
  · apply ContinuousOn.circleIntegrable (by norm_num)
    exact P.differentiable_aeval.continuous.continuousOn

/-- **Main theorem**: For any polynomial `P` and any bound `C` such that
    `‖z⁻¹ - P(z)‖ ≤ C` on the unit circle, we have `1 ≤ C`.

    This proves `sup_{|z|=1} |1/z - P(z)| ≥ 1` since the sup is the least
    uniform bound. -/
theorem one_le_of_uniform_bound (P : Polynomial ℂ) {C : ℝ}
    (hC : ∀ z ∈ sphere (0 : ℂ) 1, ‖z⁻¹ - Polynomial.aeval z P‖ ≤ C) :
    1 ≤ C := by
  have hintegral := circleIntegral_inv_sub_polynomial P
  have hnorm_integral :
      ‖∮ (z : ℂ) in C(0, 1), (fun z => z⁻¹ - Polynomial.aeval z P) z‖ = 2 * Real.pi := by
    rw [hintegral]
    simp [Complex.norm_I, Real.pi_pos.le, abs_of_nonneg]
  have hML :
      ‖∮ (z : ℂ) in C(0, 1), (fun z => z⁻¹ - Polynomial.aeval z P) z‖ ≤
        2 * Real.pi * 1 * C :=
    circleIntegral.norm_integral_le_of_norm_le_const (by norm_num : (0:ℝ) ≤ 1) hC
  have h2π_le : 2 * Real.pi ≤ 2 * Real.pi * 1 * C := hnorm_integral ▸ hML
  have h2π_pos : 0 < 2 * Real.pi := by positivity
  have hC_ge_1 : 1 ≤ C := by
    have h1 : 2 * Real.pi ≤ 2 * Real.pi * C := by linarith
    have h2π_ne : (2 * Real.pi) ≠ 0 := h2π_pos.ne'
    field_simp
    nlinarith [h2π_pos, h1]
  exact hC_ge_1

/-- **Main theorem**: `sup_{|z|=1} |1/z - P(z)| ≥ 1` for any polynomial `P`.

    The function `1/z` cannot be uniformly approximated by polynomials on the
    unit circle. This follows because the contour integral separates `1/z`
    (integral `= 2πi`) from all polynomials (integral `= 0` by Cauchy's theorem). -/
theorem sup_inv_sub_polynomial_ge_one (P : Polynomial ℂ) :
    1 ≤ ⨆ z ∈ sphere (0 : ℂ) 1, ‖z⁻¹ - Polynomial.aeval z P‖ := by
  -- The ciSup is an upper bound of the values on the sphere.
  -- We prove this by converting to the subtype form.
  have h_bdd : BddAbove (Set.range fun (s : sphere (0 : ℂ) 1) =>
    ‖s.val⁻¹ - Polynomial.aeval s.val P‖) := by
    refine ⟨1 + ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖, ?_⟩
    rintro a ⟨s, rfl⟩
    have hs1 : ‖s.val‖ = 1 := (mem_sphere_zero_iff_norm.mp s.coe_prop)
    have hsi : ‖s.val⁻¹‖ ≤ 1 := by rw [norm_inv, hs1, inv_one]
    have hP : Polynomial.aeval s.val P =
        ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • s.val ^ k := by
      rw [Polynomial.aeval_eq_sum_range]
    have hns : ‖∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • s.val ^ k‖ ≤
        ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by
        rw [norm_smul, norm_pow, hs1, one_pow, mul_one])
    linarith [norm_sub_le s.val⁻¹ (Polynomial.aeval s.val P), hsi, hP ▸ hns]
  haveI h_ne : Nonempty (sphere (0 : ℂ) 1) :=
    ⟨1, mem_sphere_zero_iff_norm.mpr (by norm_num : ‖(1:ℂ)‖ = 1)⟩
  have h0 : 0 ≤ ⨆ (s : sphere (0 : ℂ) 1), ‖s.val⁻¹ - Polynomial.aeval s.val P‖ :=
    (norm_nonneg _).trans (le_ciSup h_bdd
      (show sphere (0:ℂ) 1 from ⟨1, mem_sphere_zero_iff_norm.mpr (by norm_num)⟩))
  -- Convert ⨆ z ∈ sphere to ⨆ s : Subtype
  have h_eq : (⨆ (s : sphere (0 : ℂ) 1), ‖s.val⁻¹ - Polynomial.aeval s.val P‖) =
      ⨆ z ∈ sphere (0 : ℂ) 1, ‖z⁻¹ - Polynomial.aeval z P‖ :=
    ciSup_subtype (p := fun z => z ∈ sphere (0 : ℂ) 1)
      (f := fun s => ‖s.val⁻¹ - Polynomial.aeval s.val P‖) h_bdd
      (by rw [Real.sSup_empty]; exact h0)
  rw [← h_eq]
  -- Now the ciSup over the subtype IS an upper bound, via le_ciSup.
  -- Apply one_le_of_uniform_bound with C = ciSup.
  apply one_le_of_uniform_bound P
  intro z hz
  exact le_ciSup h_bdd ⟨z, hz⟩

end
