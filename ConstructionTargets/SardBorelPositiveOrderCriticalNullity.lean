import ConstructionTargets.SardOrderOneCriticalNullity
import ConstructionTargets.SardBorelClassicalCriticalNullityPredicate

open Set MeasureTheory
open SardClassicalRegularityAdmissibilityProbe
universe u v

def BorelPositiveOrderCriticalNullityAtDimension (d : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E], Module.finrank ℝ E = d →
    ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F],
      ∀ (μ : Measure F), μ.IsAddHaarMeasure →
      ∀ (order : ℕ), 1 ≤ order → SardOrderAdmissible d (Module.finrank ℝ F) order →
      ∀ (f : E → F) (s : Set E), (∀ x ∈ s, ContDiffAt ℝ order f x) →
        μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0

theorem borelPositiveOrderCriticalNullity_iff_highOrder (d : ℕ) :
    BorelPositiveOrderCriticalNullityAtDimension.{u,v} d ↔
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E], Module.finrank ℝ E = d →
      ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F],
      ∀ (μ : Measure F), μ.IsAddHaarMeasure →
      ∀ (order : ℕ), 2 ≤ order → SardOrderAdmissible d (Module.finrank ℝ F) order →
      ∀ (f : E → F) (s : Set E), (∀ x ∈ s, ContDiffAt ℝ order f x) →
        μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  constructor
  · intro h E _ _ _ hd F _ _ _ _ _ μ hμ order ho
    exact h E hd F μ hμ order (by omega)
  · intro h E _ _ _ hd F _ _ _ _ _ μ hμ order ho hadm f s hf
    letI := hμ
    by_cases htwo : 2 ≤ order
    · exact h E hd F μ hμ order htwo hadm f s hf
    · have heq : order = 1 := by omega
      subst order
      exact orderOne_criticalImage_zero μ f s (by simpa only [hd] using hadm) hf

theorem borelPositiveOrderCriticalNullity_zero :
    BorelPositiveOrderCriticalNullityAtDimension.{u,v} 0 := by
  intro E _ _ _ hd F _ _ _ _ _ μ hμ order _ hadm f s hf
  exact SardBorelClassicalCriticalNullityPredicateProbe.borelClassicalCriticalNullity_zero
    E hd F μ hμ order hadm f s hf

#print axioms borelPositiveOrderCriticalNullity_iff_highOrder
#print axioms borelPositiveOrderCriticalNullity_zero
