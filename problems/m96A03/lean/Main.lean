import Mathlib

/-!
# APM m96A03

## Statement repairs

None.

## Encoding notes

The first part uses Mathlib's `OrthonormalBasis` on the genuine complex
`L²` space over the restricted Lebesgue measure.  The second part is stated
on an arbitrary complex Hilbert space.
-/

open scoped BigOperators ENNReal Interval
open MeasureTheory Set

theorem apm_m96a03
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] :
    (∀ (a b : ℝ) (hab : a ≤ b)
      (u : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict (Icc a b))))
      (t : ℝ), t ∈ Icc a b →
        ∑' n : ℕ, ‖∫ s in a..t, u n s‖ ^ 2 = t - a) ∧
    (∀ (A : X →L[ℂ] X) (b : X), IsClosed (Set.range A) →
      ((∃ x : X, A x = b) ↔ ∀ y : X, A.adjoint y = 0 → inner ℂ b y = 0)) := by
  sorry
