import ConstructionTargets.SardFiniteOrderRankZeroSameSpaceEndpointNullity
import ConstructionTargets.SardContinuousLinearEquivImageNullity

open Set MeasureTheory

noncomputable section

namespace SardFiniteOrderRankZeroEqualDimensionEndpointNullityProbe

theorem measure_image_zero_of_rankZero_equivTarget
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μE : Measure E) (μF : Measure F)
    [Measure.IsAddHaarMeasure μE] [Measure.IsAddHaarMeasure μF]
    (e : F ≃L[ℝ] E) (f : E → F) (s : Set E)
    (hunique : UniqueDiffOn ℝ s)
    (hf : ∀ x ∈ s, DifferentiableWithinAt ℝ f s x)
    (hzero : s ⊆ rankStratum (fun x => (fderivWithin ℝ f s x).toLinearMap) 0) :
    μF (f '' s) = 0 := by
  have hcompDiff : ∀ x ∈ s, DifferentiableWithinAt ℝ (e ∘ f) s x := by
    intro x hx
    exact e.differentiableAt.comp_differentiableWithinAt x (hf x hx)
  have hcompZero :
      s ⊆ rankStratum (fun x => (fderivWithin ℝ (e ∘ f) s x).toLinearMap) 0 := by
    intro x hx
    have hrank := hzero hx
    change Module.finrank ℝ
      (LinearMap.range (fderivWithin ℝ f s x).toLinearMap) = 0 at hrank
    have hrange : LinearMap.range (fderivWithin ℝ f s x).toLinearMap = ⊥ :=
      Submodule.finrank_eq_zero.mp hrank
    have hlinear : (fderivWithin ℝ f s x).toLinearMap = 0 :=
      LinearMap.range_eq_bot.mp hrange
    have hfzero : fderivWithin ℝ f s x = 0 := by
      ext y
      exact LinearMap.congr_fun hlinear y
    have hderiv :
        fderivWithin ℝ (e ∘ f) s x =
          (e : F →L[ℝ] E).comp (fderivWithin ℝ f s x) := by
      exact (e.hasFDerivAt.comp_hasFDerivWithinAt x
        (hf x hx).hasFDerivWithinAt).fderivWithin (hunique x hx)
    change Module.finrank ℝ
      (LinearMap.range (fderivWithin ℝ (e ∘ f) s x).toLinearMap) = 0
    rw [hderiv, hfzero]
    have hz : ((e : F →L[ℝ] E).comp (0 : E →L[ℝ] F)).toLinearMap = 0 := by
      ext y
      simp
    rw [hz, LinearMap.range_zero]
    simp
  have hz : μE ((e ∘ f) '' s) = 0 :=
    SardFiniteOrderRankZeroSameSpaceEndpointNullityProbe.measure_image_zero_of_rankZero_sameSpace
      μE (e ∘ f) s hcompDiff hcompZero
  apply SardContinuousLinearEquivImageNullityProbe.ContinuousLinearEquiv.measure_zero_of_image_zero_addHaar
    e μF μE (f '' s)
  simpa [Function.comp_def, image_image] using hz

#print axioms measure_image_zero_of_rankZero_equivTarget

end SardFiniteOrderRankZeroEqualDimensionEndpointNullityProbe
