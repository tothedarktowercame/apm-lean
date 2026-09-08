import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory

namespace SardVolumeNullityToAddHaarProbe

/-- A volume-null subset of a finite-dimensional real inner-product space is
null for every additive Haar measure on that space. -/
theorem addHaar_eq_zero_of_volume_eq_zero
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (s : Set F) (hs : volume s = 0) : μ s = 0 := by
  rw [Measure.isAddLeftInvariant_eq_smul μ volume, Measure.smul_apply, hs]
  simp

#print axioms addHaar_eq_zero_of_volume_eq_zero

end SardVolumeNullityToAddHaarProbe
