import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # Positive ball measure is nonzero and finite -/

open MeasureTheory Metric

/-- A positive-radius ball has nonzero, finite measure under the standard
open-positive and locally finite hypotheses used by the packing argument. -/
theorem ball_measure_ne_zero_and_ne_top
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [Measure.IsOpenPosMeasure μ] [IsLocallyFiniteMeasure μ]
    (x : X) {r : ℝ} (hr : 0 < r) :
    μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ⊤ := by
  exact ⟨(measure_ball_pos μ x hr).ne', measure_ball_lt_top.ne⟩

#print axioms ball_measure_ne_zero_and_ne_top
