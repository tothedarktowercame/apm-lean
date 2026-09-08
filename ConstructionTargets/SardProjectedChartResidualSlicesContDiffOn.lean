import ConstructionTargets.SardProjectedChartInverseSliceContDiffOn
import ConstructionTargets.SardProjectedChartInverseSliceCompositionContDiff

namespace SardProjectedChartResidualSlicesContDiffOnProbe

variable {E F C G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Smoothness on the chart source and target supplies the complete indexed
family of residual inverse-slice regularity hypotheses. -/
theorem contDiffAt_residual_inverseSlices_of_contDiffOn
    (chart : OpenPartialHomeomorph E (C × G)) (f : E → F) (Q : F →L[ℝ] S)
    (n : WithTop ℕ∞)
    (hsymm : ContDiffOn ℝ n chart.symm chart.target)
    (hf : ContDiffOn ℝ n f chart.source) :
    ∀ r z, z ∈ {z | (r, z) ∈ chart.target} →
      ContDiffAt ℝ n (fun w : G => Q (f (chart.symm (r, w)))) z := by
  intro r z hz
  apply SardProjectedChartInverseSliceCompositionContDiffProbe.contDiffAt_residual_comp_inverseChartSlice
  · exact SardProjectedChartInverseSliceContDiffOnProbe.contDiffAt_inverseSlice_of_contDiffOn_symm
      chart n hsymm r z hz
  · exact (hf (chart.symm (r, z)) (chart.map_target hz)).contDiffAt
      (chart.open_source.mem_nhds (chart.map_target hz))

#print axioms contDiffAt_residual_inverseSlices_of_contDiffOn

end SardProjectedChartResidualSlicesContDiffOnProbe
