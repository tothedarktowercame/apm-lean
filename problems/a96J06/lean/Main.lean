import Mathlib
import ConstructionTargets.SchwarzEquality

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

def apm_a96J06_poly (N : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X + ∑ n ∈ Finset.Icc 2 N,
    Polynomial.C (c n) * Polynomial.X ^ n

lemma apm_a96J06_eval_poly (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    (apm_a96J06_poly N c).eval z = apm_a96J06_polynomial N c z := by
  simp [apm_a96J06_poly, apm_a96J06_polynomial, Polynomial.eval_finset_sum]

lemma apm_a96J06_coeff_top (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℂ) :
    (apm_a96J06_poly N c).coeff N = c N := by
  have h1N : 1 ≠ N := by omega
  have hx : (Polynomial.X : Polynomial ℂ).coeff N = 0 := by
    rw [Polynomial.coeff_X]
    simp [h1N]
  simp [apm_a96J06_poly, Polynomial.finset_sum_coeff, hN, hx]

theorem apm_a96j06
    (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℂ) (hcN : c N ≠ 0) :
    ∀ r : ℝ, 0 < r →
      ∃ ζ : ℂ, ‖ζ‖ < r ∧ r < ‖apm_a96J06_polynomial N c ζ‖ := by
  /- CLOSER HOP 1 BOUNDARY.

  `ConstructionTargets.SchwarzEquality.eqOn_deriv_mul` supplies the decisive
  rigidity theorem.  The helpers above now package the displayed finite sum as
  an actual complex polynomial, prove its evaluation formula, and expose its
  nonzero top coefficient.  Consequently the remaining route is precise:
  negate the desired witness for a fixed positive `r`, rescale by `z ↦ r*z`
  to obtain a unit-disk self-map fixing zero with derivative one, apply Schwarz
  equality, and use `Polynomial.eq_of_infinite_eval_eq` on the resulting open
  disk identity.  Comparing coefficient `N` with `apm_a96J06_coeff_top` then
  contradicts `hcN`.

  The live bridge is the Lean assembly of that rescaling: differentiability
  and derivative normalization of the coerced polynomial, conversion of the
  negated existential into `MapsTo` for the open unit disk (including strict
  boundary handling), and an explicit infinite subset of the complex disk for
  `Polynomial.eq_of_infinite_eval_eq`.  Mathlib and solved-sibling searches
  found the individual facts but no already compiled theorem combining them.
  The frozen statement is unchanged.
  -/
  sorry
