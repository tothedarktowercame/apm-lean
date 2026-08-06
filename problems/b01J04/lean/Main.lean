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
  -- PARTIAL (closer hop 1): bridge still open.
  -- Part (a) simultaneous diagonalization ⟺ commute: BLOCKED.
  --   Mathlib has diagonalizability machinery (`Matrix.IsDiag`, eigenvectors) but
  --   no simultaneous diagonalization theorem. The proof requires showing that
  --   commuting diagonalizable matrices share a common eigenbasis via invariant
  --   subspace decomposition — a substantial proof (~50 lines) not in Mathlib.
  -- Part (b) A⁻¹ = q(A): TRACTABLE via Cayley-Hamilton.
  --   Mathlib HAS `aeval_self_charpoly` (Cayley-Hamilton) in `LinearAlgebra/Charpoly/Basic.lean`.
  --   For IsUnit A: charpoly has nonzero constant term (= det A ≠ 0).
  --   From p(A) = 0: write A·(c₁I + c₂A + ... + cₙAⁿ⁻¹) = -c₀I, giving A⁻¹ as polynomial in A.
  --   This is ~15-20 lines but blocked by part (a) in the conjunction.
  -- Consulted: LEMMA-INDEX.md (no relevant entries), Mathlib Charpoly/Basic.lean
  -- (found `aeval_self_charpoly`, `aeval_eq_aeval_mod_charpoly`).
  sorry
