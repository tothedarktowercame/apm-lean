import ConstructionTargets.SardZeroDimensionalBorelCriticalImage

open Set MeasureTheory
universe u v

namespace SardHighOrderPredicateProbe

/-- High-order threshold: an order at least `d * (d + 1) + 2` suffices
unconditionally at source dimension `d`. -/
def sardHighOrderThreshold (d : ℕ) : ℕ := d * (d + 1) + 2

/-- Finite-order Morse--Sard nullity at source dimension `d`, for all
admissible orders above the high-order threshold. -/
def HighOrderNullityAtDimension (d : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E],
    Module.finrank ℝ E = d →
    ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F],
      ∀ (μF : Measure F), Measure.IsAddHaarMeasure μF →
      ∀ (order : ℕ),
        SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
          d (Module.finrank ℝ F) order →
        sardHighOrderThreshold d ≤ order →
        ∀ (f : E → F) (s : Set E),
          (∀ x ∈ s, ContDiffAt ℝ order f x) →
          μF (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0

theorem sardHighOrderThreshold_mono {d e : ℕ} (h : e ≤ d) :
    sardHighOrderThreshold e ≤ sardHighOrderThreshold d := by
  unfold sardHighOrderThreshold
  nlinarith [h]

end SardHighOrderPredicateProbe
