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
  basis through `A` and normalizing the weighted inner products. I searched
  the `OrthogonalFamily`, eigenspace direct-sum, `HilbertBasis`, adjoint of
  continuous-linear equivalences, and isometry/unitarity APIs, but did not
  find the required infinite-dimensional basis constructor in this pass.
  -/
  sorry
