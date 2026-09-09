import ConstructionTargets.SardFiniteOrderRankZeroEqualDimensionEndpointNullity

open Set MeasureTheory

noncomputable section

namespace SardFiniteOrderRankZeroOrderOneEndpointNullityProbe

theorem measure_image_zero_of_rankZero_orderOne_endpoint
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μE : Measure E) (μF : Measure F)
    [Measure.IsAddHaarMeasure μE] [Measure.IsAddHaarMeasure μF]
    (f : E → F) (s : Set E) (order : ℕ)
    (horder : order = 1)
    (hendpoint : order * Module.finrank ℝ F = Module.finrank ℝ E)
    (hunique : UniqueDiffOn ℝ s)
    (hf : ∀ x ∈ s, DifferentiableWithinAt ℝ f s x)
    (hzero : s ⊆ rankStratum (fun x => (fderivWithin ℝ f s x).toLinearMap) 0) :
    μF (f '' s) = 0 := by
  subst order
  have hfinrank : Module.finrank ℝ F = Module.finrank ℝ E := by
    simpa using hendpoint
  let e : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hfinrank
  exact
    SardFiniteOrderRankZeroEqualDimensionEndpointNullityProbe.measure_image_zero_of_rankZero_equivTarget
      μE μF e f s hunique hf hzero

#print axioms measure_image_zero_of_rankZero_orderOne_endpoint

end SardFiniteOrderRankZeroOrderOneEndpointNullityProbe
