import ConstructionTargets.SardProjectedChartIndexedResidualSliceZero
import ConstructionTargets.SardProjectedChartResidualSlicesContDiffOn

namespace SardProjectedChartResidualSliceNullityDataProbe

variable {E F C G S R : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup R] [NormedSpace ℝ R]

/-- Two-sided chart regularity and indexed zero residual derivatives provide
the regularity and projected-zero inputs required by compact fiber nullity. -/
theorem residual_inverseSlice_nullity_data
    (chart : OpenPartialHomeomorph E (C × G)) (f : E → F) (Q : F →L[ℝ] S)
    (hsymm : ContDiffOn ℝ 1 chart.symm chart.target)
    (hf : ContDiffOn ℝ 1 f chart.source)
    (hzero : ∀ c z, (c, z) ∈ chart.target →
      HasFDerivAt (fun w : G => Q (f (chart.symm (c, w)))) (0 : G →L[ℝ] S) z)
    (P : S →L[ℝ] R) :
    (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
      ContDiffAt ℝ 1 (fun w : G => Q (f (chart.symm (c, w)))) z) ∧
    (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
      HasFDerivAt (P ∘ fun w : G => Q (f (chart.symm (c, w))))
        (0 : G →L[ℝ] R) z) := by
  constructor
  · exact SardProjectedChartResidualSlicesContDiffOnProbe.contDiffAt_residual_inverseSlices_of_contDiffOn
      chart f Q 1 hsymm hf
  · intro c z hz
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_zero] using
      P.hasFDerivAt.comp z (hzero c z hz)

#print axioms residual_inverseSlice_nullity_data

end SardProjectedChartResidualSliceNullityDataProbe
