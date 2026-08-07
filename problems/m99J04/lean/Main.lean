import Mathlib

/-!
# APM m99J04

## Statement repairs

None.

## Encoding questions

“Basis” means a Hilbert basis, not an algebraic Hamel basis. The generalized
eigenvectors are encoded as the image of a Hilbert basis under the given continuous
linear equivalence; this is precisely a topological (Riesz) basis and does not falsely
claim that its vectors are orthonormal in the original inner product.
-/

noncomputable section

def apm_m99j04_conjugate
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) (T : H →L[𝕜] H) : H →L[𝕜] H :=
  (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp
    (T.comp A.toContinuousLinearMap)

def apm_m99j04_weight
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) : H →L[𝕜] H :=
  (ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap).comp
    A.symm.toContinuousLinearMap

def apm_m99j04_HasEigenHilbertBasis
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) : Prop :=
  ∃ (ι : Type) (b : HilbertBasis ι 𝕜 H) (eigenvalue : ι → 𝕜),
    ∀ i, star (eigenvalue i) = eigenvalue i ∧
      T (b i) = eigenvalue i • b i

lemma apm_m99j04_weight_inner
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) (x y : H) :
    inner 𝕜 (apm_m99j04_weight A (A x)) (A y) = inner 𝕜 x y := by
  simp [apm_m99j04_weight, ContinuousLinearMap.adjoint_inner_left]

/-- An eigenvector of the congruence transports to a generalized eigenvector
for the original operator and the induced weight. -/
lemma apm_m99j04_generalized_eigenvector
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) (T : H →L[𝕜] H) (w : H) (eigenvalue : 𝕜)
    (hw : apm_m99j04_conjugate A T w = eigenvalue • w) :
    T (A w) = eigenvalue • apm_m99j04_weight A (A w) := by
  have h := congrArg
    (fun z => ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap z) hw
  have hinv :
      (ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.adjoint A.toContinuousLinearMap) =
        ContinuousLinearMap.id 𝕜 H := by
    rw [← ContinuousLinearMap.adjoint_comp]
    congr 1
    ext x
    simp
  simp only [apm_m99j04_conjugate, ContinuousLinearMap.comp_apply,
    map_smul] at h
  change ((ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.adjoint A.toContinuousLinearMap)) (T (A w)) =
      eigenvalue • ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap w at h
  rw [hinv] at h
  simpa [apm_m99j04_weight] using h

theorem apm_m99j04
    (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H)
    (hTcompact : IsCompactOperator T)
    (hTself : ContinuousLinearMap.adjoint T = T)
    (A : H ≃L[𝕜] H) :
    apm_m99j04_HasEigenHilbertBasis T ∧
      IsCompactOperator (apm_m99j04_conjugate A T) ∧
      ContinuousLinearMap.adjoint (apm_m99j04_conjugate A T) =
        apm_m99j04_conjugate A T ∧
      ∃ (ι : Type) (w : HilbertBasis ι 𝕜 H) (eigenvalue : ι → 𝕜),
        (∀ i, star (eigenvalue i) = eigenvalue i) ∧
        (∀ i,
          T (A (w i)) =
            eigenvalue i • apm_m99j04_weight A (A (w i))) ∧
        (∀ i, inner 𝕜 (apm_m99j04_weight A (A (w i))) (A (w i)) = 1) ∧
        (∀ i j, i ≠ j →
          inner 𝕜 (apm_m99j04_weight A (A (w i))) (A (w j)) = 0) ∧
        (Orthonormal 𝕜 (fun i => A (w i)) ↔
          (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp
              A.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 H) := by
  have hconjugate_compact : IsCompactOperator (apm_m99j04_conjugate A T) := by
    simpa [apm_m99j04_conjugate, Function.comp_def] using
      (hTcompact.comp_clm A.toContinuousLinearMap).clm_comp
        (ContinuousLinearMap.adjoint A.toContinuousLinearMap)
  have hconjugate_self :
      ContinuousLinearMap.adjoint (apm_m99j04_conjugate A T) =
        apm_m99j04_conjugate A T := by
    rw [apm_m99j04_conjugate, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, hTself,
      ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.comp_assoc _ _ _
  /-
  Boundary: compactness and self-adjointness of the congruence `A† T A` are
  proved above. Completing the frozen theorem requires turning Mathlib's
  compact spectral theorem
  `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` into a
  single `HilbertBasis` indexed across all eigenspaces, then transporting that
  basis through `A`; the weighted inner-product transport identity needed for
  its normalization and orthogonality is proved above. Closer hop 1 also proves
  `apm_m99j04_generalized_eigenvector`, which transports each ordinary
  eigenvector equation for `A† T A` to the frozen generalized equation for
  `T` and the weight. I searched
  the `OrthogonalFamily`, eigenspace direct-sum, `HilbertBasis`, adjoint of
  continuous-linear equivalences, and isometry/unitarity APIs, but did not
  find the required infinite-dimensional basis constructor in this pass.
  -/
  sorry
