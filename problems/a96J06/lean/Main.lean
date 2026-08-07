import Mathlib

/-!
# APM a96J06 — a normalized polynomial expands every centered disk

## Statement repairs

None.

## Encoding questions

None. The polynomial is the finite sum printed in the source, with its
coefficient sequence and terminal nonzero coefficient explicit.
-/

noncomputable section

def apm_a96J06_polynomial (N : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  z + ∑ n ∈ Finset.Icc 2 N, c n * z ^ n

theorem apm_a96j06
    (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℂ) (hcN : c N ≠ 0) :
    ∀ r : ℝ, 0 < r →
      ∃ ζ : ℂ, ‖ζ‖ < r ∧ r < ‖apm_a96J06_polynomial N c ζ‖ := by
  sorry
