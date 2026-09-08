import ConstructionTargets.SardOpenPartialHomeomorphDerivativeRightInverse

namespace SardProjectedChartDerivativeSurjectiveProbe

variable {E R G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The first coordinate of a differentiable open product chart has surjective
derivative whenever its inverse is differentiable at the corresponding point. -/
theorem fst_comp_range_eq_top_of_chart_derivatives
    (chart : OpenPartialHomeomorph E (R × G)) (y : R × G) (hy : y ∈ chart.target)
    (D : E →L[ℝ] R × G) (H : (R × G) →L[ℝ] E) (P : E →L[ℝ] R)
    (hD : HasFDerivAt chart D (chart.symm y))
    (hH : HasFDerivAt chart.symm H y)
    (hP : P = (ContinuousLinearMap.fst ℝ R G).comp D) :
    P.range = ⊤ := by
  apply SardProjectedDerivativeSurjectiveOfRightInverseProbe.fst_comp_range_eq_top_of_rightInverse
    D H P hP
  exact SardOpenPartialHomeomorphDerivativeRightInverseProbe.derivative_comp_inverseDerivative_eq_id
    chart y hy D H hD hH

#print axioms fst_comp_range_eq_top_of_chart_derivatives

end SardProjectedChartDerivativeSurjectiveProbe
