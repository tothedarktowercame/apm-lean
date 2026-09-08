import ConstructionTargets.SardFiniteOrderRankLocusLocalAggregation
import ConstructionTargets.SardCriticalRankStrataNull

open Set MeasureTheory

namespace SardFiniteOrderCriticalRankLociAggregationProbe

/-- Pointwise null-image neighborhoods on every exact derivative-rank locus
aggregate to nullity of the full critical image. -/
theorem criticalImage_null_of_pointwise_rankLocus_open
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (f' : E → E →ₗ[ℝ] F)
    (hlocal : ∀ r : Fin (Module.finrank ℝ F), ∀ x ∈ rankStratum f' r,
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ μ (f '' (rankStratum f' r ∩ U)) = 0) :
    μ (f '' criticalSet f') = 0 := by
  apply criticalImage_null_of_rankStrata_null μ f f'
  intro r
  apply SardFiniteOrderRankLocusLocalAggregationProbe.measure_image_zero_of_rankLocus_pointwise_open
  exact hlocal r

#print axioms criticalImage_null_of_pointwise_rankLocus_open

end SardFiniteOrderCriticalRankLociAggregationProbe
