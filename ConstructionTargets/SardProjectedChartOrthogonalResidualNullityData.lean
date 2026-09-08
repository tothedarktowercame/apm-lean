import ConstructionTargets.SardProjectedChartResidualSliceNullityData

noncomputable section

namespace SardProjectedChartOrthogonalResidualNullityDataProbe

variable {E F C G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Orthogonal residual-slice zero derivatives and two-sided chart regularity
give the paired regularity and zero-derivative data used by compact nullity. -/
theorem orthogonalResidual_inverseSlice_nullity_data
    (L : E →L[ℝ] F) (chart : OpenPartialHomeomorph E (C × G)) (f : E → F)
    (hsymm : ContDiffOn ℝ 1 chart.symm chart.target)
    (hf : ContDiffOn ℝ 1 f chart.source)
    (hzero : ∀ c z, (c, z) ∈ chart.target →
      HasFDerivAt
        (fun w : G => (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
          (f (chart.symm (c, w))))
        (0 : G →L[ℝ] (LinearMap.range L.toLinearMap)ᗮ) z) :
    (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
      ContDiffAt ℝ 1
        (fun w : G => (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
          (f (chart.symm (c, w)))) z) ∧
    (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
      HasFDerivAt
        ((ContinuousLinearMap.id ℝ (LinearMap.range L.toLinearMap)ᗮ) ∘
          fun w : G => (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
            (f (chart.symm (c, w))))
        (0 : G →L[ℝ] (LinearMap.range L.toLinearMap)ᗮ) z) := by
  exact SardProjectedChartResidualSliceNullityDataProbe.residual_inverseSlice_nullity_data
    chart f (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection hsymm hf hzero
    (ContinuousLinearMap.id ℝ (LinearMap.range L.toLinearMap)ᗮ)

#print axioms orthogonalResidual_inverseSlice_nullity_data

end SardProjectedChartOrthogonalResidualNullityDataProbe
