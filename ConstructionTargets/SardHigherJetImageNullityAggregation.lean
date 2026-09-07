import ConstructionTargets.SardLocalNullitySecondCountableAggregation
import ConstructionTargets.SardHigherJetLocusDecomposition

open Set MeasureTheory

namespace SardHigherJetImageNullityAggregationProbe

/-- Nullity of the Taylor-flat locus and every nonzero-jet locus through order
`k` aggregates to nullity of the whole localized source image. -/
theorem image_null_of_flatThrough_and_nonzeroJetLoci
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (k : ℕ)
    (hflat : μ (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K k) = 0)
    (hjet : ∀ i ∈ Set.Icc 1 k,
      μ (f '' SardHigherJetLocusDecompositionProbe.nonzeroJetLocus f K i) = 0) :
    μ (f '' K) = 0 := by
  rw [SardHigherJetLocusDecompositionProbe.eq_flatThrough_union_iUnion_nonzeroJetLocus
    f K k, image_union]
  apply measure_union_null hflat
  rw [image_iUnion]
  apply measure_iUnion_null
  intro i
  rw [image_iUnion]
  exact measure_iUnion_null fun hi => hjet i hi

#print axioms image_null_of_flatThrough_and_nonzeroJetLoci
end SardHigherJetImageNullityAggregationProbe
