import ConstructionTargets.SardBorelOverlapTargetEquivTransfer

open Set MeasureTheory
universe u v

theorem localSet_criticalImage_zero_of_borel_overlap_normed_spaces
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (s : Set E) (k : ℕ)
    (hf : ∀ x ∈ s, ContDiffAt ℝ (k + 2) f x)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hind : ∀ d < Module.finrank ℝ E,
      SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension.{u,v} d)
    (hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
      Module.finrank ℝ F + (k + 2) + 1) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  let H := EuclideanSpace ℝ (ULift.{v} (Fin (Module.finrank ℝ F)))
  have hdim : Module.finrank ℝ F = Module.finrank ℝ H := by simp [H]
  let e : F ≃L[ℝ] H := (LinearEquiv.ofFinrankEq F H hdim).toContinuousLinearEquiv
  exact localSet_criticalImage_zero_of_borel_overlap_target_equiv
    e μ (volume : Measure H) f s k hf hadm hind hoverlap

#print axioms localSet_criticalImage_zero_of_borel_overlap_normed_spaces
