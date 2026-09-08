import ConstructionTargets.SardProjectedChartDerivativeSurjective

namespace SardSmoothProjectedChartFirstDerivativeSurjectiveProbe

variable {E R G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- On a chart smooth in both directions, the derivative of any function equal
to its first coordinate is surjective at every source point. -/
theorem range_eq_top_of_eq_fst_smooth_chart
    (chart : OpenPartialHomeomorph E (R × G))
    (hchart : ContDiffOn ℝ 1 chart chart.source)
    (hinv : ContDiffOn ℝ 1 chart.symm chart.target)
    (q : E → R) (z : E) (hz : z ∈ chart.source) (P : E →L[ℝ] R)
    (hq : HasFDerivAt q P z)
    (heq : q = fun x => (chart x).1) :
    P.range = ⊤ := by
  have hD : HasFDerivAt chart (fderiv ℝ chart z) z :=
    (hchart.differentiableOn_one.differentiableAt (chart.open_source.mem_nhds hz)).hasFDerivAt
  have htarget : chart z ∈ chart.target := chart.map_source hz
  have hH : HasFDerivAt chart.symm (fderiv ℝ chart.symm (chart z)) (chart z) :=
    (hinv.differentiableOn_one.differentiableAt
      (chart.open_target.mem_nhds htarget)).hasFDerivAt
  have hfirst : HasFDerivAt q
      ((ContinuousLinearMap.fst ℝ R G).comp (fderiv ℝ chart z)) z := by
    rw [heq]
    exact hD.fst
  have hP : P = (ContinuousLinearMap.fst ℝ R G).comp (fderiv ℝ chart z) :=
    hq.unique hfirst
  apply SardProjectedChartDerivativeSurjectiveProbe.fst_comp_range_eq_top_of_chart_derivatives
    chart (chart z) htarget (fderiv ℝ chart z) (fderiv ℝ chart.symm (chart z)) P
  · simpa only [chart.left_inv hz] using hD
  · exact hH
  · exact hP

#print axioms range_eq_top_of_eq_fst_smooth_chart

end SardSmoothProjectedChartFirstDerivativeSurjectiveProbe
