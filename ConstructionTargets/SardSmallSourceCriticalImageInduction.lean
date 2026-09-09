import ConstructionTargets.SardRankZeroSmallSourceNullity
import ConstructionTargets.SardFiniteOrderCriticalImageOfRankZeroNullity

open Set MeasureTheory
universe u v

theorem smallSource_local_criticalImage_zero_of_lowerDimension_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (f : E → F) (s : Set E) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 1))
    (hdim : Module.finrank ℝ E ≤ 2 * Module.finrank ℝ F)
    (hind : ∀ e < Module.finrank ℝ E,
      SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  have hzero := rankZero_image_zero_of_sourceDim_le_twice_targetDim μ f k hf hadm hdim
  have hall := SardFiniteOrderCriticalImageOfRankZeroNullityProbe.measure_criticalImage_zero_of_rankZero_finiteOrder
    μ f (k + 1) (Module.finrank ℝ E) hf (by omega) hind rfl hadm hzero
  exact measure_mono_null (Set.image_mono inter_subset_right) hall

#print axioms smallSource_local_criticalImage_zero_of_lowerDimension_induction
