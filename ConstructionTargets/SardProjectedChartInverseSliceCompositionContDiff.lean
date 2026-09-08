import ConstructionTargets.SardCompactProjectedChartImageNullity

namespace SardProjectedChartInverseSliceCompositionContDiffProbe

variable {E F C G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup C]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Smoothness of a chart inverse slice and of the ambient map passes through a
continuous-linear residual target coordinate. -/
theorem contDiffAt_residual_comp_inverseChartSlice
    (chart : OpenPartialHomeomorph E (C × G)) (f : E → F) (Q : F →L[ℝ] S)
    (n : WithTop ℕ∞) (r : C) (z : G)
    (hslice : ContDiffAt ℝ n (fun w : G => chart.symm (r, w)) z)
    (hf : ContDiffAt ℝ n f (chart.symm (r, z))) :
    ContDiffAt ℝ n (fun w : G => Q (f (chart.symm (r, w)))) z := by
  exact Q.contDiff.contDiffAt.comp z (hf.comp z hslice)

#print axioms contDiffAt_residual_comp_inverseChartSlice

end SardProjectedChartInverseSliceCompositionContDiffProbe
