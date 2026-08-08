import Mathlib

/-!
# APM a95J03 — winding number of a trigonometric polynomial

## Statement repairs

None.

## Encoding questions

Mathlib has no directly usable integer-valued winding-number definition for a
parametrized path of this form. The index is therefore encoded by its genuine
normalized contour integral. The theorem asserts that this complex integral
is an integer and that the integer lies between `-N` and `N`.
-/

open Complex Polynomial
open scoped Interval Real BigOperators

noncomputable section

def apm_a95J03_trigPoly (a : ℤ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  (Finset.Icc (-(N : ℤ)) N).sum
    (fun n ↦ a n * Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)))

def apm_a95J03_algPoly (a : ℤ → ℂ) (N : ℕ) : Polynomial ℂ :=
  (Finset.range (2 * N + 1)).sum
    (fun k ↦ Polynomial.C (a ((k : ℤ) - N)) * Polynomial.X ^ k)

/-- The algebraic polynomial obtained after clearing the `N` negative powers
has degree at most `2N`. Reused from the sound algebraic layer at commit
`1bf56f4`; unlike that commit's opaque winding-number placeholder, this lemma
applies unchanged to the repaired encoding. -/
lemma apm_a95J03_algPoly_degree_le (a : ℤ → ℂ) (N : ℕ) :
    (apm_a95J03_algPoly a N).natDegree ≤ 2 * N := by
  unfold apm_a95J03_algPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_X_pow_le _ k).trans (by
    simp only [Finset.mem_range] at hk
    omega)

/-- Subtracting `z Xⁿ` preserves the `2N` degree bound. -/
lemma apm_a95J03_algPoly_sub_degree_le
    (a : ℤ → ℂ) (N : ℕ) (z : ℂ) :
    (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).natDegree ≤
      2 * N := by
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  apply max_le
  · exact apm_a95J03_algPoly_degree_le a N
  · by_cases hz : z = 0
    · simp [hz, Polynomial.natDegree_zero]
    · rw [Polynomial.natDegree_C_mul_X_pow N z hz]
      omega

lemma apm_a95J03_trigPoly_hasDerivAt (a : ℤ → ℂ) (N : ℕ) (t : ℝ) :
    HasDerivAt (apm_a95J03_trigPoly a N)
      ((Finset.Icc (-(N : ℤ)) N).sum fun n ↦
        a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) *
          (Complex.I * (n : ℂ)))) t := by
  unfold apm_a95J03_trigPoly
  apply HasDerivAt.fun_sum
  intro n _
  convert (((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * (n : ℂ))).comp_ofReal.cexp
    |>.const_mul (a n)) using 1 <;> simp [id] <;> ring

lemma apm_a95J03_fderiv_apply_one (a : ℤ → ℂ) (N : ℕ) (t : ℝ) :
    (fderiv ℝ (apm_a95J03_trigPoly a N) t) 1 =
      (Finset.Icc (-(N : ℤ)) N).sum (fun n ↦
        a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) *
          (Complex.I * (n : ℂ)))) := by
  have h := apm_a95J03_trigPoly_hasDerivAt a N t
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    congrArg (fun L : ℝ →L[ℝ] ℂ ↦ L 1) h.hasFDerivAt.fderiv

lemma apm_a95J03_trigPoly_eq_laurent (a : ℤ → ℂ) (N : ℕ) (t : ℝ) :
    apm_a95J03_trigPoly a N t =
      (Finset.Icc (-(N : ℤ)) N).sum fun n ↦
        a n * Complex.exp (Complex.I * (t : ℂ)) ^ n := by
  unfold apm_a95J03_trigPoly
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

def apm_a95J03_windingIntegral (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * Complex.I)⁻¹) *
    ∫ t in (0 : ℝ)..2 * Real.pi,
      (fderiv ℝ γ t) 1 / (γ t - z)

theorem apm_a95j03 {a : ℤ → ℂ} {N : ℕ}
    (hN : a (-(N : ℤ)) ≠ 0 ∨ a (N : ℤ) ≠ 0)
    {z : ℂ}
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_a95J03_trigPoly a N t ≠ z) :
    ∃ k : ℤ,
      apm_a95J03_windingIntegral (apm_a95J03_trigPoly a N) z = (k : ℂ) ∧
      -(N : ℤ) ≤ k ∧ k ≤ N := by
  /-
  CLOSER HOP 1: historical commits `d8c8079`--`1bf56f4` do not prove the
  repaired theorem: their `windingNumber` is an opaque definition equal to
  zero.  The sound algebraic portion has nevertheless been ported above.
  `apm_a95J03_algPoly_degree_le` and
  `apm_a95J03_algPoly_sub_degree_le` now compile the sharp degree-`2N` bound
  for the polynomial obtained after clearing the negative Fourier powers.

  CLOSER HOP 2 (partial): the real-calculus side is now explicit.
  `apm_a95J03_trigPoly_hasDerivAt` differentiates the finite Fourier sum,
  `apm_a95J03_fderiv_apply_one` rewrites the exact frozen `fderiv ℝ`
  expression, and `apm_a95J03_trigPoly_eq_laurent` identifies the exponential
  parametrization with the corresponding integer-power Laurent sum.

  Renewed inspection of `ConstructionTargets.CircleParam`, Mathlib's unfolded
  `circleIntegral`, and `ConstructionTargets.Rouche` confirms that the
  parametrization and argument-principle endpoints exist separately. The live
  bridge is now the finite-sum reindexing that proves the cleared-polynomial
  identity, followed by the logarithmic-derivative product rule for its
  `X⁻ᴺ` factor and conversion of the divisor sum to a root count bounded by
  `2N`. No searched helper assembles those Laurent/polynomial and multiplicity
  steps. The frozen statement is unchanged and no defect was found.
  -/
  sorry
