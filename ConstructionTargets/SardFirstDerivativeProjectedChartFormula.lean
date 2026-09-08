import ConstructionTargets.SardFirstDerivativeRankPieceProjectedDefiningData
import ConstructionTargets.SardLocalRankNormalForm
import ConstructionTargets.SardProjectedComplementedStrictDerivativeData
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
namespace SardFirstDerivativeProjectedImplicitFunctionDataProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local instance derivativeRangeCompleteSpace (L : E →L[ℝ] F) :
    CompleteSpace (LinearMap.range L.toLinearMap) := by
  letI := L.toLinearMap.finiteDimensional_range
  exact (LinearMap.range L.toLinearMap).complete_of_finiteDimensional.completeSpace_coe

/-- The projected local rank chart with its exact forward coordinate formula
retained, rather than only its source membership. -/
theorem exists_projected_localRankNormalForm_with_formula
    (f : E → F) (x : E) (L : E →L[ℝ] F) (hf : HasStrictFDerivAt f L x) :
    ∃ e : OpenPartialHomeomorph E
        ((LinearMap.range L.toLinearMap) ×
          ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker),
      x ∈ e.source ∧
      (e : E →
        (LinearMap.range L.toLinearMap) ×
          ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker) =
        fun y =>
          ((LinearMap.range L.toLinearMap).orthogonalProjection (f y),
            ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker.orthogonalProjection y) := by
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
  have h := SardProjectedImplicitFunctionDataProbe.projected_complemented_strictDerivative_data
    f x L hf
  let φ := @ImplicitFunctionData.mk ℝ inferInstance E inferInstance inferInstance inferInstance
    R inferInstance inferInstance hR G inferInstance inferInstance hG
    (fun y => R.orthogonalProjection (f y)) A
    (fun y => G.orthogonalProjection y) B x h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  obtain ⟨e, hxe, hformula, _⟩ :=
    @localRankNormalForm_of_complemented_minor E R G inferInstance inferInstance
      inferInstance inferInstance inferInstance hR inferInstance inferInstance hG φ
  exact ⟨e, hxe, hformula⟩

#print axioms exists_projected_localRankNormalForm_with_formula

end SardFirstDerivativeProjectedImplicitFunctionDataProbe
