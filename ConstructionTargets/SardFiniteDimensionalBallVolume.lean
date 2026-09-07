import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Exact volume of finite-dimensional closed balls -/

open MeasureTheory Metric

/-- The Borel add-Haar volume of a closed ball in a nontrivial finite-dimensional
real inner-product space, exposing its radius-to-finrank scaling factor. -/
theorem finiteDimensional_volume_closedBall_formula
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (x : E) (r : ℝ) :
    volume (closedBall x r) =
      ENNReal.ofReal r ^ Module.finrank ℝ E *
        ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
          Real.Gamma (Module.finrank ℝ E / 2 + 1)) := by
  exact InnerProductSpace.volume_closedBall x r

#print axioms finiteDimensional_volume_closedBall_formula
