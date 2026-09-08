import ConstructionTargets.SardProjectedChartResidualSlicesContDiffOn
import ConstructionTargets.SardRankDropRegularityAdmissibility

namespace SardFiniteOrderProjectedSliceInductionDataProbe

variable {E F C G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- A projected residual slice retains the original finite differentiability
order, while classical Sard admissibility survives the common rank drop. -/
theorem finiteOrder_projectedSlice_induction_data
    (chart : OpenPartialHomeomorph E (C × G)) (f : E → F) (Q : F →L[ℝ] S)
    (order sourceDim targetDim rank : ℕ)
    (hsymm : ContDiffOn ℝ order chart.symm chart.target)
    (hf : ContDiffOn ℝ order f chart.source)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      sourceDim targetDim order)
    (hrSource : rank ≤ sourceDim) (hrTarget : rank ≤ targetDim) :
    (∀ r z, z ∈ {z | (r, z) ∈ chart.target} →
      ContDiffAt ℝ order (fun w : G => Q (f (chart.symm (r, w)))) z) ∧
    SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (sourceDim - rank) (targetDim - rank) order := by
  exact ⟨SardProjectedChartResidualSlicesContDiffOnProbe.contDiffAt_residual_inverseSlices_of_contDiffOn
    chart f Q order hsymm hf,
    SardRankDropRegularityAdmissibilityProbe.sardOrderAdmissible_sub_rank
      hadm hrSource hrTarget⟩

#print axioms finiteOrder_projectedSlice_induction_data

end SardFiniteOrderProjectedSliceInductionDataProbe
