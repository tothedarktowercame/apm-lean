import ConstructionTargets.SardEqualDimensionAmbientCriticalNullity
import ConstructionTargets.SardLowerDimensionAmbientImageNullity
import ConstructionTargets.SardClassicalRegularityAdmissibility

open Set MeasureTheory
open SardClassicalRegularityAdmissibilityProbe

theorem orderOne_criticalImage_zero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (s : Set E)
    (hadm : SardOrderAdmissible (Module.finrank ℝ E) (Module.finrank ℝ F) 1)
    (hf : ∀ x ∈ s, ContDiffAt ℝ 1 f x) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  have hdiff : ∀ x ∈ s, DifferentiableAt ℝ f x :=
    fun x hx => (hf x hx).differentiableAt (by norm_num)
  have hle : Module.finrank ℝ E ≤ Module.finrank ℝ F := by
    unfold SardOrderAdmissible at hadm
    omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact measure_mono_null (image_mono inter_subset_left)
      (lowerDimension_ambient_image_zero μ f s hlt hdiff)
  · exact equalDimension_ambient_criticalImage_zero μ f s heq hdiff

#print axioms orderOne_criticalImage_zero
