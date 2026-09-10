import Mathlib.MeasureTheory.Measure.Hausdorff

open MeasureTheory MeasureTheory.Measure
open scoped MeasureTheory

namespace ConstructionTargets.HausdorffBorelInstanceCoherence

variable {X : Type*} [TopologicalSpace X]

theorem measurableSpace_eq_of_borel
    (m₁ m₂ : MeasurableSpace X)
    (b₁ : @BorelSpace X _ m₁) (b₂ : @BorelSpace X _ m₂) :
    m₁ = m₂ := by
  exact b₁.measurable_eq.trans b₂.measurable_eq.symm

section
variable {Y : Type*} [EMetricSpace Y]

theorem hausdorffMeasure_apply_eq_of_borel
    (m₁ m₂ : MeasurableSpace Y)
    (b₁ : @BorelSpace Y _ m₁) (b₂ : @BorelSpace Y _ m₂)
    (d : ℝ) (s : Set Y) :
    (@hausdorffMeasure Y _ m₁ b₁ d) s =
      (@hausdorffMeasure Y _ m₂ b₂ d) s := by
  have h : m₁ = m₂ := measurableSpace_eq_of_borel m₁ m₂ b₁ b₂
  subst m₂
  congr

end

#print axioms measurableSpace_eq_of_borel
#print axioms hausdorffMeasure_apply_eq_of_borel

end ConstructionTargets.HausdorffBorelInstanceCoherence
