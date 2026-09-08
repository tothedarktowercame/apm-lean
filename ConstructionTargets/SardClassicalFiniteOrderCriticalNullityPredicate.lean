import ConstructionTargets.SardClassicalRegularityAdmissibility
import ConstructionTargets.SardFinrankStrongInductionClosure

open Set MeasureTheory

noncomputable section
namespace SardClassicalFiniteOrderCriticalNullityPredicateProbe

universe u v

def ClassicalCriticalNullityAtDimension (d : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E],
    Module.finrank ℝ E = d →
    ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F],
      ∀ (μF : Measure F), Measure.IsAddHaarMeasure μF →
      ∀ (order : ℕ),
        SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
          d (Module.finrank ℝ F) order →
        ∀ (f : E → F) (s : Set E),
          (∀ x ∈ s, ContDiffAt ℝ order f x) →
          μF (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0

theorem classicalCriticalNullity_all_dimensions
    (hstep : ∀ d : ℕ,
      (∀ e : ℕ, e < d → ClassicalCriticalNullityAtDimension.{u,v} e) →
      ClassicalCriticalNullityAtDimension.{u,v} d) :
    ∀ d : ℕ, ClassicalCriticalNullityAtDimension.{u,v} d := by
  intro d
  exact Nat.strong_induction_on d hstep

#print axioms classicalCriticalNullity_all_dimensions

end SardClassicalFiniteOrderCriticalNullityPredicateProbe
