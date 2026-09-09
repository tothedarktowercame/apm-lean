import ConstructionTargets.SardBorelOverlapSourceEquivTransfer
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set MeasureTheory
universe u v

theorem localSet_criticalImage_zero_of_borel_overlap_normed_source
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
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
  let G := EuclideanSpace ℝ (ULift.{u} (Fin (Module.finrank ℝ E)))
  have hdim : Module.finrank ℝ G = Module.finrank ℝ E := by simp [G]
  let e : G ≃L[ℝ] E := (LinearEquiv.ofFinrankEq G E hdim).toContinuousLinearEquiv
  exact localSet_criticalImage_zero_of_borel_overlap_source_equiv
    e μ f s k hf hadm hind hoverlap

#print axioms localSet_criticalImage_zero_of_borel_overlap_normed_source
