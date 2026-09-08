import ConstructionTargets.SardFiniteRegularityDimensionAdmissibility
import ConstructionTargets.SardFinrankStrongInductionClosure

open Set MeasureTheory

noncomputable section
namespace SardFiniteOrderCriticalNullityPredicateProbe

universe u v

def FiniteOrderCriticalNullityAtDimension (d : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E],
    Module.finrank ℝ E = d →
    ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F],
      ∀ (μF : Measure F), Measure.IsAddHaarMeasure μF →
      ∀ (order : ℕ),
        SardFiniteRegularityDimensionAdmissibilityProbe.FiniteOrderAdmissible
          d (Module.finrank ℝ F) order →
        ∀ (f : E → F) (s : Set E),
          (∀ x ∈ s, ContDiffAt ℝ order f x) →
          μF (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0

theorem finiteOrderCriticalNullity_all_dimensions
    (hstep : ∀ d : ℕ,
      (∀ e : ℕ, e < d → FiniteOrderCriticalNullityAtDimension.{u,v} e) →
      FiniteOrderCriticalNullityAtDimension.{u,v} d) :
    ∀ d : ℕ, FiniteOrderCriticalNullityAtDimension.{u,v} d := by
  intro d
  exact Nat.strong_induction_on d hstep

#print axioms finiteOrderCriticalNullity_all_dimensions

end SardFiniteOrderCriticalNullityPredicateProbe
