import ConstructionTargets.SardContinuousAddEquivQuasiMeasurePreserving
import ConstructionTargets.SardEquivImageNullityTransfer

open Set MeasureTheory

namespace SardContinuousLinearEquivImageNullityProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [LocallyCompactSpace F] [SecondCountableTopology F]

/-- A continuous real-linear equivalence reflects nullity of its image between
additive Haar measures. -/
theorem ContinuousLinearEquiv.measure_zero_of_image_zero_addHaar
    (e : E ≃L[ℝ] F) (μ : Measure E) (ν : Measure F)
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    (s : Set E) (hs : ν (e '' s) = 0) :
    μ s = 0 := by
  apply SardEquivImageNullityTransferProbe.measure_zero_of_equiv_image_zero
    μ ν e.toEquiv
  · exact SardContinuousAddEquivQuasiMeasurePreservingProbe.ContinuousAddEquiv.quasiMeasurePreserving_addHaar
      e.toContinuousAddEquiv μ ν
  · exact hs

#print axioms ContinuousLinearEquiv.measure_zero_of_image_zero_addHaar

end SardContinuousLinearEquivImageNullityProbe
