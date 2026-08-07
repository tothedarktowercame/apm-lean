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
  sorry
