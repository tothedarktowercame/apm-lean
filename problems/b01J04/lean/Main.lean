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

private theorem apm_b01J04_simultaneous_of_commute
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hA : apmMatrixDiagonalizable A) (hB : apmMatrixDiagonalizable B)
    (hAB : A * B = B * A) :
    ∃ T : Matrix n n ℂ, IsUnit T ∧
      (T * A * T⁻¹).IsDiag ∧ (T * B * T⁻¹).IsDiag := by
  /-
  Closer-hop-3 boundary: Mathlib does prove the simultaneous generalized-
  eigenspace decomposition for commuting endomorphisms via
  `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
  (used in sibling `b93J03`).  The hypotheses `hA` and `hB` imply that the
  generalized eigenspaces are ordinary eigenspaces.  However, no API was
  found that converts this joint eigenspace `iSup/iInf` decomposition into a
  single basis and then into the precise conjugation witness required here.

  Searches covered `LEMMA-INDEX.md`, `Eigenspace/Pi.lean`,
  `Eigenspace/Matrix.lean`, `Eigenspace/Semisimple.lean`, matrix `IsDiag`, all
  closed artifacts, and git history.  Completing this locally requires the
  missing basis-by-direct-sum assembly (or a dimension induction over common
  eigenspaces), which remains beyond this closer hop.  The statement is
  mathematically correct.
  -/
  sorry

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
  constructor
  · intro n _ _ A B hA hB
    constructor
    · rintro ⟨T, hT, hDA, hDB⟩
      have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
      have hTiT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hdet
      have hTTi : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hdet
      have hdcomm : (T * A * T⁻¹) * (T * B * T⁻¹) =
          (T * B * T⁻¹) * (T * A * T⁻¹) := by
        rw [← hDA.diagonal_diag, ← hDB.diagonal_diag]
        exact (Matrix.commute_diagonal _ _).eq
      have hprod (X Y : Matrix n n ℂ) :
          (T * X * T⁻¹) * (T * Y * T⁻¹) = T * (X * Y) * T⁻¹ := by
        calc
          (T * X * T⁻¹) * (T * Y * T⁻¹) =
              T * X * (T⁻¹ * T) * Y * T⁻¹ := by noncomm_ring
          _ = T * (X * Y) * T⁻¹ := by rw [hTiT]; noncomm_ring
      rw [hprod A B, hprod B A] at hdcomm
      have hsand (X : Matrix n n ℂ) : T⁻¹ * (T * X * T⁻¹) * T = X := by
        calc
          T⁻¹ * (T * X * T⁻¹) * T = (T⁻¹ * T) * X * (T⁻¹ * T) := by
            noncomm_ring
          _ = X := by rw [hTiT]; simp
      have := congrArg (fun X ↦ T⁻¹ * X * T) hdcomm
      simpa only [hsand] using this
    · exact apm_b01J04_simultaneous_of_commute A B hA hB
  · intro k _ n _ _ A hA
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
    have hc : A.charpoly.coeff 0 ≠ 0 := by
      intro hc
      apply hdet.ne_zero
      rw [Matrix.det_eq_sign_charpoly_coeff, hc, mul_zero]
    let r : k[X] := A.charpoly.divX
    have hrel : A * aeval A r + algebraMap k (Matrix n n k) (A.charpoly.coeff 0) = 0 := by
      dsimp [r]
      calc
        A * aeval A A.charpoly.divX +
            algebraMap k (Matrix n n k) (A.charpoly.coeff 0) =
            aeval A (X * A.charpoly.divX + C (A.charpoly.coeff 0)) := by
              rw [map_add, map_mul]
              simp
        _ = aeval A A.charpoly := by rw [A.charpoly.X_mul_divX_add]
        _ = 0 := Matrix.aeval_self_charpoly A
    let q : k[X] := C (-(A.charpoly.coeff 0)⁻¹) * r
    refine ⟨q, ?_⟩
    have hright : A * aeval A q = 1 := by
      dsimp [q]
      rw [map_mul, aeval_C]
      have hc_inv : (-(A.charpoly.coeff 0)⁻¹) * A.charpoly.coeff 0 = -1 := by
        field_simp
      calc
        A * (algebraMap k (Matrix n n k) (-(A.charpoly.coeff 0)⁻¹) * aeval A r) =
            algebraMap k (Matrix n n k) (-(A.charpoly.coeff 0)⁻¹) *
              (A * aeval A r) := by
                rw [← Matrix.mul_assoc,
                  (Algebra.commutes (-(A.charpoly.coeff 0)⁻¹) A).symm,
                  Matrix.mul_assoc]
        _ = algebraMap k (Matrix n n k) (-(A.charpoly.coeff 0)⁻¹) *
              (-algebraMap k (Matrix n n k) (A.charpoly.coeff 0)) := by
                rw [eq_neg_of_add_eq_zero_left hrel]
        _ = 1 := by
          rw [← map_neg, ← map_mul]
          simp [hc]
    have hdet' : IsUnit A.det := hdet
    calc
      A⁻¹ = A⁻¹ * 1 := by rw [Matrix.mul_one]
      _ = A⁻¹ * (A * aeval A q) := by rw [hright]
      _ = aeval A q := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hdet', Matrix.one_mul]

#print axioms apm_b01j04
