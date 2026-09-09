import Mathlib.MeasureTheory.Function.Jacobian
import ConstructionTargets.SardCriticalRankStrata

open Set MeasureTheory

noncomputable section

namespace SardFiniteOrderRankZeroSameSpaceEndpointNullityProbe

theorem measure_image_zero_of_rankZero_sameSpace
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → E) (s : Set E)
    (hf : ∀ x ∈ s, DifferentiableWithinAt ℝ f s x)
    (hzero : s ⊆ rankStratum (fun x => (fderivWithin ℝ f s x).toLinearMap) 0) :
    μ (f '' s) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (f' := fun x => fderivWithin ℝ f s x)
  · intro x hx
    exact (hf x hx).hasFDerivWithinAt
  · intro x hx
    have hrank := hzero hx
    change Module.finrank ℝ
      (LinearMap.range (fderivWithin ℝ f s x).toLinearMap) = 0 at hrank
    have hrange : LinearMap.range (fderivWithin ℝ f s x).toLinearMap = ⊥ :=
      Submodule.finrank_eq_zero.mp hrank
    have hlinear : (fderivWithin ℝ f s x).toLinearMap = 0 :=
      LinearMap.range_eq_bot.mp hrange
    have hcontinuous : fderivWithin ℝ f s x = 0 := by
      ext y
      exact LinearMap.congr_fun hlinear y
    rw [hcontinuous]
    change LinearMap.det (0 : E →ₗ[ℝ] E) = 0
    simp

#print axioms measure_image_zero_of_rankZero_sameSpace

end SardFiniteOrderRankZeroSameSpaceEndpointNullityProbe
