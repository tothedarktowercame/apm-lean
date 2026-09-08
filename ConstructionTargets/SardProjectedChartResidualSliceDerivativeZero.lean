import ConstructionTargets.SardProjectedChartResidualSlicesContDiffOn

namespace SardProjectedChartResidualSliceDerivativeZeroProbe

variable {E F G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- If the residual coordinate annihilates the derivative along a chart slice,
the residualized slice has zero derivative. -/
theorem hasFDerivAt_zero_residual_comp_slice
    (f : E → F) (slice : G → E) (Q : F →L[ℝ] S)
    (z : G) (D : E →L[ℝ] F) (J : G →L[ℝ] E)
    (hf : HasFDerivAt f D (slice z)) (hslice : HasFDerivAt slice J z)
    (hzero : Q.comp (D.comp J) = 0) :
    HasFDerivAt (fun w => Q (f (slice w))) (0 : G →L[ℝ] S) z := by
  simpa [hzero] using Q.hasFDerivAt.comp z (hf.comp z hslice)

#print axioms hasFDerivAt_zero_residual_comp_slice

end SardProjectedChartResidualSliceDerivativeZeroProbe
