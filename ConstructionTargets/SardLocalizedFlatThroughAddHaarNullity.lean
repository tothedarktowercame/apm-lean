import ConstructionTargets.SardLocalizedFlatThroughTaylorNullity
import ConstructionTargets.SardVolumeNullityToAddHaar

open Metric Set MeasureTheory
open scoped ENNReal NNReal

namespace SardLocalizedFlatThroughAddHaarNullityProbe

theorem localized_flatThrough_image_addHaar_eq_zero
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K) (z : E) (R : ℝ)
    (hbounded : K ⊆ closedBall z R) (k d : ℕ) (hd : 0 < d)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E + d)
    (hf : ContDiff ℝ (k + 1) f)
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hkt : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ ⊤)
    (q : ℝ≥0) (hq0 : 0 < q) (hq1 : q < 1) :
    μF (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K k) = 0 := by
  apply SardVolumeNullityToAddHaarProbe.addHaar_eq_zero_of_volume_eq_zero
  exact SardLocalizedFlatThroughTaylorNullityProbe.localized_flatThrough_image_volume_eq_zero
    f K hK z R hbounded k d hd hexp hf hk0 hkt q hq0 hq1

#print axioms localized_flatThrough_image_addHaar_eq_zero

end SardLocalizedFlatThroughAddHaarNullityProbe
