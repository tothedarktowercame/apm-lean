import ConstructionTargets.SardSameSpaceAmbientCriticalNullity
import ConstructionTargets.SardSourceEquivCriticalImage

open Set MeasureTheory

theorem equalDimension_ambient_criticalImage_zero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (s : Set E)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  let e : F ≃L[ℝ] E := (LinearEquiv.ofFinrankEq F E hdim.symm).toContinuousLinearEquiv
  have hreg : ∀ x ∈ e ⁻¹' s, DifferentiableAt ℝ (f ∘ e) x := by
    intro x hx
    exact (hf (e x) hx).comp x e.differentiableAt
  have hnull := sameSpace_ambient_criticalImage_zero μ (f ∘ e) (e ⁻¹' s) hreg
  rw [criticalImage_eq_of_source_continuousLinearEquiv e f s hf] at hnull
  exact hnull

#print axioms equalDimension_ambient_criticalImage_zero
