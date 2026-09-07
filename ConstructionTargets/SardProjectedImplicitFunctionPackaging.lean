import ConstructionTargets.SardLocalRankNormalForm
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
namespace SardProjectedImplicitFunctionPackagingProbe


variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem projectedData (f : E → F) (x : E) (L : E →L[ℝ] F)
    (hf : HasStrictFDerivAt f L x) :
    let R := LinearMap.range L.toLinearMap
    let A : E →L[ℝ] R := R.orthogonalProjection.comp L
    let G := A.ker
    let B : E →L[ℝ] G := G.orthogonalProjection
    HasStrictFDerivAt (fun y => R.orthogonalProjection (f y)) A x ∧
      HasStrictFDerivAt (fun y => G.orthogonalProjection y) B x ∧
      A.range = ⊤ ∧ B.range = ⊤ ∧ IsCompl A.ker B.ker := by
  dsimp only
  let R := LinearMap.range L.toLinearMap
  let A : E →L[ℝ] R := R.orthogonalProjection.comp L
  let G := A.ker
  letI hG : CompleteSpace G := by infer_instance
  let B : E →L[ℝ] G := G.orthogonalProjection
  have hA : A.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    rcases y.property with ⟨z, hz⟩
    refine ⟨z, Subtype.ext ?_⟩
    have hp : R.orthogonalProjection (L z) = y := by
      rw [show L z = (y : F) from hz]
      exact R.orthogonalProjection_mem_subspace_eq_self y
    exact congrArg Subtype.val hp
  have hB : B.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨y, G.orthogonalProjection_mem_subspace_eq_self y⟩
  have hc : IsCompl A.ker B.ker := by
    rw [show B.ker = Gᗮ by
      change G.orthogonalProjection.ker = Gᗮ
      exact G.ker_orthogonalProjection]
    exact G.isCompl_orthogonal_of_hasOrthogonalProjection
  exact ⟨R.orthogonalProjection.hasStrictFDerivAt.comp x hf,
    G.orthogonalProjection.hasStrictFDerivAt, hA, hB, hc⟩

local instance derivativeRangeCompleteSpace (L : E →L[ℝ] F) :
    CompleteSpace (LinearMap.range L.toLinearMap) := by
  letI := L.toLinearMap.finiteDimensional_range
  exact (LinearMap.range L.toLinearMap).complete_of_finiteDimensional.completeSpace_coe

/-- The projected derivative data packages locally as `ImplicitFunctionData` and
feeds the banked local rank-normal-form theorem without an added hypothesis. -/
theorem exists_projected_localRankNormalForm
    (f : E → F) (x : E) (L : E →L[ℝ] F) (hf : HasStrictFDerivAt f L x) :
    ∃ e : OpenPartialHomeomorph E
        ((LinearMap.range L.toLinearMap) ×
          ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker),
      x ∈ e.source := by
  let R := LinearMap.range L.toLinearMap
  let hR : CompleteSpace R := by
    letI := L.toLinearMap.finiteDimensional_range
    exact R.complete_of_finiteDimensional.completeSpace_coe
  letI := hR
  let A : E →L[ℝ] R := R.orthogonalProjection.comp L
  let G := A.ker
  let hG : CompleteSpace G := by infer_instance
  letI := hG
  let B : E →L[ℝ] G := G.orthogonalProjection
  have h := projectedData f x L hf
  let φ := @ImplicitFunctionData.mk ℝ inferInstance E inferInstance inferInstance inferInstance
    R inferInstance inferInstance hR G inferInstance inferInstance hG
    (fun y => R.orthogonalProjection (f y)) A
    (fun y => G.orthogonalProjection y) B x h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  rcases (@localRankNormalForm_of_complemented_minor E R G inferInstance inferInstance
    inferInstance inferInstance inferInstance hR inferInstance inferInstance hG φ) with
    ⟨e, he, _⟩
  exact ⟨e, he⟩

#print axioms exists_projected_localRankNormalForm
end SardProjectedImplicitFunctionPackagingProbe
