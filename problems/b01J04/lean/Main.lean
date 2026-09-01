import Mathlib

open Matrix Polynomial

noncomputable section

universe u

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

/-- Commuting semisimple endomorphisms decompose the space as the sum of their
simultaneous *ordinary* eigenspaces.  Mathlib's family theorem is stated for
maximal generalized eigenspaces; semisimplicity is exactly what removes that
extra layer. -/
private theorem apm_b01J04_iSup_iInf_eigenspace_eq_top
    {ι K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j : ι ↦ Commute (f i) (f j))
    (hsemi : ∀ i, (f i).IsSemisimple) :
    ⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i) = ⊤ := by
  have hgeneralized :
      ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
    apply
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        f hcomm
    intro i
    exact Module.End.iSup_maxGenEigenspace_eq_top (f i)
  simpa only [((Module.End.isFinitelySemisimple_iff_isSemisimple).mpr
    (hsemi _)).maxGenEigenspace_eq_eigenspace] using hgeneralized

/-- The simultaneous ordinary eigenspaces in the preceding decomposition are
independent, so choosing bases in each nonzero summand and concatenating them
is the remaining common-eigenbasis construction. -/
private theorem apm_b01J04_iSupIndep_iInf_eigenspace
    {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j : ι ↦ Commute (f i) (f j))
    (hsemi : ∀ i, (f i).IsSemisimple) :
    iSupIndep fun χ : ι → K ↦ ⨅ i, (f i).eigenspace (χ i) := by
  have hmaps : ∀ i j φ,
      Set.MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ) := by
    intro i j φ
    apply Module.End.mapsTo_maxGenEigenspace_of_comm
    rcases eq_or_ne j i with rfl | hij
    · exact Commute.refl _
    · exact hcomm hij
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  simpa only [((Module.End.isFinitelySemisimple_iff_isSemisimple).mpr
    (hsemi _)).maxGenEigenspace_eq_eigenspace] using hind

private theorem apm_b01J04_common_eigenbasis
    {ι K : Type} {V n : Type u} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (standard : Module.Basis n K V)
    (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j : ι ↦ Commute (f i) (f j))
    (hsemi : ∀ i, (f i).IsSemisimple) :
    ∃ b : Module.Basis n K V, ∃ χ : n → ι → K,
      ∀ j i, f i (b j) = χ j i • b j := by
  classical
  let p : (ι → K) → Submodule K V := fun χ ↦ ⨅ i, (f i).eigenspace (χ i)
  have htop : ⨆ χ, p χ = ⊤ :=
    apm_b01J04_iSup_iInf_eigenspace_eq_top f hcomm hsemi
  have hind : iSupIndep p :=
    apm_b01J04_iSupIndep_iInf_eigenspace f hcomm hsemi
  let bp (χ : ι → K) := Module.Free.chooseBasis K (p χ)
  let bd : Module.Basis (Σ χ, Module.Free.ChooseBasisIndex K (p χ)) K (Π₀ χ, p χ) :=
    DFinsupp.basis bp
  let br := bd.map (hind.linearEquiv htop)
  let e : (Σ χ, Module.Free.ChooseBasisIndex K (p χ)) ≃ n :=
    Classical.choice (Cardinal.eq.mp
      (br.mk_eq_rank''.trans standard.mk_eq_rank''.symm))
  refine ⟨br.reindex e, fun j ↦ (e.symm j).1, ?_⟩
  intro j i
  rw [Module.Basis.reindex_apply]
  apply Module.End.mem_eigenspace_iff.mp
  have hb : br (e.symm j) ∈ p (e.symm j).1 := by
    have hbd : bd (e.symm j) = DFinsupp.single (e.symm j).1
        ((bp (e.symm j).1) (e.symm j).2) := by
      apply bd.repr.injective
      simp [bd, DFinsupp.basis]
    have hbr : br (e.symm j) =
        ((bp (e.symm j).1) (e.symm j).2 : p (e.symm j).1) := by
      dsimp [br]
      rw [hbd]
      simp
    rw [hbr]
    exact ((bp (e.symm j).1) (e.symm j).2).property
  dsimp only [p] at hb
  simp only [Submodule.mem_iInf] at hb
  exact hb i

private theorem apm_b01J04_diagonal_isSemisimple
    {K : Type} {n : Type u} [Field K] [Fintype n] [DecidableEq n] (d : n → K) :
    Module.End.IsSemisimple (Matrix.diagonal d).toLin' := by
  classical
  let s : Finset K := Finset.univ.image d
  let p : K[X] := ∏ a ∈ s, (X - C a)
  have haeval (q : K[X]) :
      aeval (Matrix.diagonal d) q = Matrix.diagonal (fun i ↦ q.eval (d i)) := by
    induction q using Polynomial.induction_on' with
    | add q r hq hr =>
        rw [map_add, hq, hr]
        ext i j
        by_cases hij : i = j <;> simp [hij]
    | monomial m a =>
        rw [aeval_monomial, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_pow,
          Matrix.diagonal_mul_diagonal]
        congr
        funext i
        simp
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := p) ?_ ?_
  · rw [show p = s.prod fun a ↦ X - C a by simp [p]]
    exact (Polynomial.separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h ↦ h).squarefree
  · change (aeval (Matrix.toLinAlgEquiv' (Matrix.diagonal d))) p = 0
    rw [Polynomial.aeval_algHom_apply]
    rw [← map_zero Matrix.toLinAlgEquiv']
    congr 1
    rw [haeval]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply, if_pos, Matrix.zero_apply]
      simp only [p, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      apply Finset.prod_eq_zero (i := d i)
      · simp [s]
      · simp
    · simp [hij]

private theorem apm_b01J04_isSemisimple_of_diagonalizable
    {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : apmMatrixDiagonalizable A) :
    Module.End.IsSemisimple A.toLin' := by
  obtain ⟨T, hT, hD⟩ := hA
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  let D := T * A * T⁻¹
  let e := T.toLinearEquiv (Pi.basisFun ℂ n) hdet
  have hsemiD : Module.End.IsSemisimple D.toLin' := by
    rw [show D = Matrix.diagonal D.diag by
      exact hD.diagonal_diag.symm]
    exact apm_b01J04_diagonal_isSemisimple D.diag
  have he : e.toLinearMap.comp A.toLin' = D.toLin'.comp e.toLinearMap := by
    change Matrix.toLin' T ∘ₗ Matrix.toLin' A = Matrix.toLin' D ∘ₗ Matrix.toLin' T
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
    congr 1
    dsimp [D]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul T hdet, Matrix.mul_one]
  exact (e.isSemisimple_iff A.toLin' D.toLin' he).mpr hsemiD

private theorem apm_b01J04_simultaneous_of_commute
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hA : apmMatrixDiagonalizable A) (hB : apmMatrixDiagonalizable B)
    (hAB : A * B = B * A) :
    ∃ T : Matrix n n ℂ, IsUnit T ∧
      (T * A * T⁻¹).IsDiag ∧ (T * B * T⁻¹).IsDiag := by
  classical
  let f : Fin 2 → Module.End ℂ (n → ℂ) := ![A.toLin', B.toLin']
  have hlincomm : Commute A.toLin' B.toLin' := by
    rw [commute_iff_eq, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hAB]
  have hfcomm : Pairwise fun i j : Fin 2 ↦ Commute (f i) (f j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · contradiction
    · exact hlincomm
    · exact hlincomm.symm
    · contradiction
  have hfsemi : ∀ i, (f i).IsSemisimple := by
    intro i
    fin_cases i
    · exact apm_b01J04_isSemisimple_of_diagonalizable A hA
    · exact apm_b01J04_isSemisimple_of_diagonalizable B hB
  let std := Pi.basisFun ℂ n
  obtain ⟨b, χ, hb⟩ := apm_b01J04_common_eigenbasis std f hfcomm hfsemi
  let T : Matrix n n ℂ := b.toMatrix std
  letI : Invertible T := Module.Basis.invertibleToMatrix b std
  have hTinv : T⁻¹ = std.toMatrix b := by
    rw [← Matrix.invOf_eq_nonsing_inv]
    rfl
  have hchange (M : Matrix n n ℂ) :
      T * M * T⁻¹ = LinearMap.toMatrix b b M.toLin' := by
    rw [hTinv]
    change b.toMatrix std * M * std.toMatrix b = _
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix,
      ← LinearMap.toMatrix_id_eq_basis_toMatrix]
    rw [← LinearMap.toMatrix_toLin std std M]
    change LinearMap.toMatrix std b LinearMap.id *
        LinearMap.toMatrix std std M.toLin' *
        LinearMap.toMatrix b std LinearMap.id = _
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    simp
  have hdiag (k : Fin 2) : (LinearMap.toMatrix b b (f k)).IsDiag := by
    intro i j hij
    rw [LinearMap.toMatrix_apply, hb j k]
    simp [hij]
  refine ⟨T, isUnit_of_invertible T, ?_, ?_⟩
  · rw [hchange A]
    exact hdiag 0
  · rw [hchange B]
    exact hdiag 1

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
