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
  -- PARTIAL (closer hop 2): bridge still open. Both parts remain blocked.
  -- Part (a): Simultaneous diagonalization ⟺ commute.
  --   The ⟸ direction is the hard part: if A,B commute and each is diagonalizable,
  --   they share a common eigenbasis. Proof: D⁻¹AD diagonal ⟹ D⁻¹BD commutes with
  --   D⁻¹AD ⟹ D⁻¹BD preserves each eigenspace of D⁻¹AD ⟹ restrict and diagonalize.
  --   This requires eigenspace preservation lemmas that don't exist in Mathlib.
  --   Estimated: ~60-80 lines from scratch.
  -- Part (b): A⁻¹ = q(A) for IsUnit A.
  --   Mathlib HAS `Matrix.aeval_self_charpoly` (Cayley-Hamilton, confirmed at
  --   LinearAlgebra/Matrix/Charpoly/Basic.lean:211).
  --   Also `Matrix.aeval_eq_aeval_mod_charpoly` (Coeff.lean:250).
  --   For IsUnit A: the constant term of charpoly is (-1)ⁿ·det(A) ≠ 0.
  --   So charpoly = X^n + ... + c₀X + c₀' with c₀' ≠ 0.
  --   From aeval A charpoly = 0: c₀'·I + A·(rest) = 0 ⟹ A⁻¹ = -(rest)/c₀'.
  --   This is ~20 lines. BUT: need `Matrix.charpoly_coeff_zero_eq_det` or similar,
  --   and `aeval` on Matrix gives a Matrix (not Module.End), so the algebra setup
  --   needs careful handling.
  -- Consulted: `LinearAlgebra/Matrix/Charpoly/Basic.lean` (aeval_self_charpoly),
  --   `LinearAlgebra/Matrix/Charpoly/Coeff.lean` (aeval_eq_aeval_mod_charpoly),
  --   LEMMA-INDEX.md (no relevant entries).
  sorry
