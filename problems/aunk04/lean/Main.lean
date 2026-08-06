import Mathlib

/-!
# APM aunk04 — Rouché zero count and polynomial growth of entire functions

## Statement repairs

In part (a), the source writes `f(x)` while defining a complex polynomial in
the variable `z`.  This is treated as the typographical correction `f(z)`.

## Encoding notes

The zero count uses the polynomial's root multiset, so multiplicities are
retained.  In part (b), the degree conclusion is stated without a floor
operation: every coefficient with natural index `k > m` vanishes.  This is the
direct coefficient form of `degree ≤ floor(m)`.
-/

open Set MeasureTheory
open scoped Polynomial

noncomputable def apm_aunk04_polynomial : ℂ[X] :=
  Polynomial.X ^ 4 - Polynomial.C 3 * Polynomial.X ^ 3 +
    Polynomial.X ^ 2 + Polynomial.C 6

theorem apm_aunk04 :
    (apm_aunk04_polynomial.roots.filter (fun z => ‖z‖ < 1)).card = 0 ∧
      ∀ (f : ℂ → ℂ) (A B m : ℝ),
        0 < A → 0 < B → 0 < m →
        Differentiable ℂ f →
        (∀ z : ℂ, ‖f z‖ ≤ A + B * Real.rpow ‖z‖ m) →
        ∃ p : ℂ[X],
          (∀ z : ℂ, Polynomial.eval z p = f z) ∧
          ∀ k : ℕ, m < k → p.coeff k = 0 := by
  sorry
