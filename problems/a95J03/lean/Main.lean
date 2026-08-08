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

  Unlike the old history, the current repository does contain an argument-
  principle theorem:
  `ConstructionTargets.Rouche.circleIntegral_logDeriv_eq_divisor_sum`.
  The remaining bridge is to prove the unit-circle identity between the
  trigonometric polynomial and `X⁻ᴺ * (algPoly - z Xᴺ)`, convert the frozen
  real interval integral with `fderiv ℝ` into that complex circle integral,
  and turn the divisor sum into an integer between `-N` and `N` using the
  compiled degree bound. No statement defect was found.
  -/
  sorry
