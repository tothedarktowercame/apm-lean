import Mathlib

/-!
# APM b94J02

## Statement repairs

None.

## Encoding questions

In part (c), matrix rank is a natural number while trace lies in `K`; the
printed equality is therefore encoded as equality with the natural-number cast
`(D.rank : K)`, valid in arbitrary characteristic.
-/

theorem apm_b94j02 :
    ∀ (n : ℕ) (K : Type*) [Field K]
      (A C D : Matrix (Fin n) (Fin n) K),
      0 < n →
      (∀ m : ℕ, 0 < m → A ^ m = 0 → Matrix.trace A = 0) ∧
      ((∀ B : Matrix (Fin n) (Fin n) K, Matrix.trace (B * C) = 0) → C = 0) ∧
      (D ^ 2 = D → Matrix.trace D = (D.rank : K)) := by
  sorry
