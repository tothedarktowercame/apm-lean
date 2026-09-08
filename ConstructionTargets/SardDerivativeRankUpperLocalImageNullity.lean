import ConstructionTargets.SardClosedOpenImageNullity
import ConstructionTargets.SardDerivativeRankUpperLocusClosed

open Set MeasureTheory

namespace SardDerivativeRankUpperLocalImageNullityProbe

/-- Compact image nullity aggregates on a derivative rank-at-most locus
localized to an open set. -/
theorem measure_image_zero_of_derivativeRankAtMost_inter_open_of_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (r : ℕ) (U : Set E)
    (hf : ContDiff ℝ 1 f) (hU : IsOpen U)
    (hnull : ∀ K : Set E, IsCompact K →
      K ⊆ {x | Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r} ∩ U →
      μ (f '' K) = 0) :
    μ (f '' ({x | Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r} ∩ U)) = 0 := by
  apply SardClosedOpenImageNullityProbe.measure_image_zero_of_closed_inter_open
    μ f _ U
    (SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost f r hf)
    hU hnull

#print axioms measure_image_zero_of_derivativeRankAtMost_inter_open_of_compact

end SardDerivativeRankUpperLocalImageNullityProbe
