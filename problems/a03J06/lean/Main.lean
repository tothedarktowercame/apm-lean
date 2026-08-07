import Mathlib

/-!
# APM a03J06 — entire functions of polynomial growth

## Statement repairs

None. The statement is slightly strengthened by allowing `m = 0`; the same
conclusion then says that `f` is constant.

## Encoding questions

None. The conclusion uses an actual complex polynomial and identifies the
given entire function with its evaluation function pointwise.
-/

noncomputable section

theorem apm_a03j06 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (A : ℝ) (m : ℕ)
    (hbound : ∀ z : ℂ, 1 < ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z : ℂ, f z = p.eval z := by
  sorry
