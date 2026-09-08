import ConstructionTargets.SardProjectedChartInverseSliceContDiffOn

namespace SardProjectedChartInverseSliceHasFDerivAtProbe

variable {E C G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Every fixed-first-coordinate inverse slice of a once continuously
differentiable open chart inverse has a Frechet derivative at target points. -/
theorem exists_hasFDerivAt_inverseSlice_of_contDiffOn_symm
    (chart : OpenPartialHomeomorph E (C × G))
    (hsymm : ContDiffOn ℝ 1 chart.symm chart.target)
    (r : C) (z : G) (hz : (r, z) ∈ chart.target) :
    ∃ J : G →L[ℝ] E, HasFDerivAt (fun w : G => chart.symm (r, w)) J z := by
  have hsmooth :=
    SardProjectedChartInverseSliceContDiffOnProbe.contDiffAt_inverseSlice_of_contDiffOn_symm
      chart 1 hsymm r z hz
  have hdiff : DifferentiableAt ℝ (fun w : G => chart.symm (r, w)) z :=
    hsmooth.differentiableAt (by norm_num)
  exact ⟨fderiv ℝ (fun w : G => chart.symm (r, w)) z, hdiff.hasFDerivAt⟩

#print axioms exists_hasFDerivAt_inverseSlice_of_contDiffOn_symm

end SardProjectedChartInverseSliceHasFDerivAtProbe
