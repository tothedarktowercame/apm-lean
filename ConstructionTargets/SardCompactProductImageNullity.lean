import ConstructionTargets.SardCompactImageMeasurable
import ConstructionTargets.SardProductNullityOfNullFibers

open Set MeasureTheory

namespace SardCompactProductImageNullityProbe

/-- A compact continuous product-coordinate image is product-null when all of
its vertical sections are null. -/
theorem measure_prod_image_zero_of_isCompact_continuousOn_of_fibers
    {E R S : Type*} [TopologicalSpace E]
    [TopologicalSpace R] [T2Space R] [SecondCountableTopology R]
    [MeasurableSpace R] [BorelSpace R]
    [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S]
    (μ : Measure R) (ν : Measure S) (q : E → R × S) (K : Set E)
    (hK : IsCompact K) (hq : ContinuousOn q K)
    (hsections : ∀ r, ν (Prod.mk r ⁻¹' (q '' K)) = 0) :
    μ.prod ν (q '' K) = 0 := by
  apply SardProductNullityOfNullFibersProbe.measure_prod_zero_of_forall_fiber_zero
  · exact SardCompactImageMeasurableProbe.measurableSet_image_of_isCompact_continuousOn
      q K hK hq
  · exact hsections

#print axioms measure_prod_image_zero_of_isCompact_continuousOn_of_fibers
end SardCompactProductImageNullityProbe
