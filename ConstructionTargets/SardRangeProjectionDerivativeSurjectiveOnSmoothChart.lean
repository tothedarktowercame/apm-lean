import ConstructionTargets.SardSmoothProjectedChartFirstDerivativeSurjective
import ConstructionTargets.SardRangeProjectionCoordinateDerivative

noncomputable section
namespace SardRangeProjectionDerivativeSurjectiveOnSmoothChartProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The derivative-range coordinate has surjective derivative at every source
point of a two-sided smooth projected chart with the exact coordinate formula. -/
theorem rangeProjection_comp_range_eq_top_on_smoothChart
    (f : E → F) (L D : E →L[ℝ] F)
    (chart : OpenPartialHomeomorph E ((LinearMap.range L.toLinearMap) × G))
    (hchart : ContDiffOn ℝ 1 chart chart.source)
    (hinv : ContDiffOn ℝ 1 chart.symm chart.target)
    (second : E → G)
    (hformula : (chart : E → (LinearMap.range L.toLinearMap) × G) =
      fun y => ((LinearMap.range L.toLinearMap).orthogonalProjection (f y), second y))
    (z : E) (hz : z ∈ chart.source) (hf : HasFDerivAt f D z) :
    ((LinearMap.range L.toLinearMap).orthogonalProjection.comp D).range = ⊤ := by
  let q : E → LinearMap.range L.toLinearMap :=
    fun y => (LinearMap.range L.toLinearMap).orthogonalProjection (f y)
  have hq : HasFDerivAt q
      ((LinearMap.range L.toLinearMap).orthogonalProjection.comp D) z :=
    SardRangeProjectionCoordinateDerivativeProbe.hasFDerivAt_rangeProjection_comp f z D L hf
  have heq : q = fun y => (chart y).1 := by
    funext y
    rw [congrFun hformula y]
  exact SardSmoothProjectedChartFirstDerivativeSurjectiveProbe.range_eq_top_of_eq_fst_smooth_chart
    chart hchart hinv q z hz
      ((LinearMap.range L.toLinearMap).orthogonalProjection.comp D) hq heq

#print axioms rangeProjection_comp_range_eq_top_on_smoothChart

end SardRangeProjectionDerivativeSurjectiveOnSmoothChartProbe
