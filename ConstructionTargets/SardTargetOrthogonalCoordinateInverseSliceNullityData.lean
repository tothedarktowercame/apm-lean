import ConstructionTargets.SardProjectedChartOrthogonalResidualNullityData
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

noncomputable section

namespace SardTargetOrthogonalCoordinateInverseSliceNullityDataProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Orthogonal-projection inverse-slice data is exactly the second-coordinate
inverse-slice data for the canonical range/orthogonal target equivalence. -/
theorem targetOrthogonalCoordinates_inverseSlice_nullity_data
    (L : E →L[ℝ] F)
    (chart : OpenPartialHomeomorph E ((LinearMap.range L.toLinearMap) × G))
    (f : E → F)
    (hdata :
      (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
        ContDiffAt ℝ 1
          (fun w : G => (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
            (f (chart.symm (c, w)))) z) ∧
      (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
        HasFDerivAt
          ((ContinuousLinearMap.id ℝ (LinearMap.range L.toLinearMap)ᗮ) ∘
            fun w : G => (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
              (f (chart.symm (c, w))))
          (0 : G →L[ℝ] (LinearMap.range L.toLinearMap)ᗮ) z)) :
    (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
      ContDiffAt ℝ 1
        (fun w : G =>
          (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
            (LinearMap.range L.toLinearMap) (f (chart.symm (c, w)))).2) z) ∧
    (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
      HasFDerivAt
        ((ContinuousLinearMap.id ℝ (LinearMap.range L.toLinearMap)ᗮ) ∘
          fun w : G =>
            (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
              (LinearMap.range L.toLinearMap) (f (chart.symm (c, w)))).2)
        (0 : G →L[ℝ] (LinearMap.range L.toLinearMap)ᗮ) z) := by
  constructor
  · intro c z hz
    convert hdata.1 c z hz using 1
    funext w
    exact congrArg Prod.snd
      (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply
        (LinearMap.range L.toLinearMap) (f (chart.symm (c, w))))
  · intro c z hz
    convert hdata.2 c z hz using 1
    funext w
    simp only [Function.comp_apply, ContinuousLinearMap.id_apply]
    exact congrArg Prod.snd
      (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply
        (LinearMap.range L.toLinearMap) (f (chart.symm (c, w))))

#print axioms targetOrthogonalCoordinates_inverseSlice_nullity_data

end SardTargetOrthogonalCoordinateInverseSliceNullityDataProbe
