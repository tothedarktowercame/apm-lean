import ConstructionTargets.SardZeroDimensionalBorelCriticalImage

open Set MeasureTheory
universe u v

namespace SardBorelClassicalCriticalNullityPredicateProbe

def BorelClassicalCriticalNullityAtDimension (d : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E],
    Module.finrank ℝ E = d →
    ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F],
      ∀ (μF : Measure F), Measure.IsAddHaarMeasure μF →
      ∀ (order : ℕ),
        SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
          d (Module.finrank ℝ F) order →
        ∀ (f : E → F) (s : Set E),
          (∀ x ∈ s, ContDiffAt ℝ order f x) →
          μF (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0

theorem borelClassicalCriticalNullity_zero :
    BorelClassicalCriticalNullityAtDimension.{u,v} 0 := by
  intro E _ _ _ hd F _ _ _ _ _ μ hμ order _ f s _
  letI := hμ
  exact criticalImage_zero_of_source_finrank_zero_borel μ f s hd

#print axioms borelClassicalCriticalNullity_zero

end SardBorelClassicalCriticalNullityPredicateProbe
