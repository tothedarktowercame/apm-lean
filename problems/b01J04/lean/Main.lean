import Mathlib

open Matrix Polynomial

noncomputable section

/-!
# APM b01J04

## Statement repairs

Part (a) is false as printed: a non-diagonalizable matrix commutes with itself.
The converse is repaired by adding the necessary hypotheses that `A` and `B` are
each individually diagonalizable.

## Encoding notes

Nonsingularity is `IsUnit`; diagonalization is conjugation by an invertible matrix.
-/

def apmMatrixDiagonalizable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Prop :=
  ∃ T : Matrix n n ℂ, IsUnit T ∧ (T * A * T⁻¹).IsDiag

theorem apm_b01j04 :
    (∀ (n : Type*) [Fintype n] [DecidableEq n]
      (A B : Matrix n n ℂ),
      apmMatrixDiagonalizable A → apmMatrixDiagonalizable B →
        ((∃ T : Matrix n n ℂ, IsUnit T ∧
            (T * A * T⁻¹).IsDiag ∧ (T * B * T⁻¹).IsDiag) ↔
          A * B = B * A)) ∧
    (∀ (k : Type*) [Field k]
      (n : Type*) [Fintype n] [DecidableEq n]
      (A : Matrix n n k), IsUnit A →
        ∃ q : k[X], A⁻¹ = aeval A q) := by
  sorry
