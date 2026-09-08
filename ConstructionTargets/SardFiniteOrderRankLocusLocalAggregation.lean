import ConstructionTargets.SardFiniteOrderClosedOpenLocalRankChartNullity
import ConstructionTargets.SardLocalNullitySecondCountableAggregation

open Set MeasureTheory

namespace SardFiniteOrderRankLocusLocalAggregationProbe

/-- Pointwise open neighborhoods with null localized images aggregate to
nullity of the entire rank locus in a second-countable source. -/
theorem measure_image_zero_of_rankLocus_pointwise_open
    {E F : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (s : Set E)
    (hlocal : ∀ x ∈ s, ∃ U : Set E,
      IsOpen U ∧ x ∈ U ∧ μ (f '' (s ∩ U)) = 0) :
    μ (f '' s) = 0 := by
  classical
  let U : E → Set E := fun x =>
    if hx : x ∈ s then Classical.choose (hlocal x hx) else ∅
  apply SardLocalNullitySecondCountableAggregationProbe.image_null_of_locally_image_null
    μ f s U
  · intro x hx
    simpa only [U, dif_pos hx] using (Classical.choose_spec (hlocal x hx)).1
  · intro x hx
    simpa only [U, dif_pos hx] using (Classical.choose_spec (hlocal x hx)).2.1
  · intro x hx
    simpa only [U, dif_pos hx] using (Classical.choose_spec (hlocal x hx)).2.2

#print axioms measure_image_zero_of_rankLocus_pointwise_open

end SardFiniteOrderRankLocusLocalAggregationProbe
