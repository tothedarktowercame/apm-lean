import ConstructionTargets.SardRankZeroBorelJetRangeOverlap
import ConstructionTargets.SardBorelCriticalImageOfRankZeroNullity

open Set MeasureTheory
universe u v

theorem criticalImage_zero_of_borel_jet_range_overlap_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (s : Set E) (k : ℕ)
    (hf : ContDiff ℝ (k + 2) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hind : ∀ e < Module.finrank ℝ E,
      SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension.{u,v} e)
    (hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
      Module.finrank ℝ F + (k + 2) + 1) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  have hzero := rankZero_image_zero_of_borel_jet_range_overlap_induction
    μ f k hf hadm hind hoverlap
  have hall := SardBorelCriticalImageOfRankZeroNullityProbe.measure_criticalImage_zero_of_rankZero_finiteOrder
    μ f (k + 2) (Module.finrank ℝ E) hf (by omega) hind rfl hadm hzero
  exact measure_mono_null (Set.image_mono inter_subset_right) hall

#print axioms criticalImage_zero_of_borel_jet_range_overlap_induction
