import ConstructionTargets.SardFlatThroughCompactLocalization
import ConstructionTargets.SardFlatThroughTaylorNullity

open Metric Set MeasureTheory
open scoped ENNReal NNReal

namespace SardLocalizedFlatThroughTaylorNullityProbe

/-- Compact localization and Taylor covering combine to give nullity of the
exact flat-through locus directly from the localized source hypotheses. -/
theorem localized_flatThrough_image_volume_eq_zero
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (z : E) (R : ℝ)
    (hbounded : K ⊆ closedBall z R) (k d : ℕ) (hd : 0 < d)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E + d)
    (hf : ContDiff ℝ (k + 1) f)
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hkt : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ ⊤)
    (q : ℝ≥0) (hq0 : 0 < q) (hq1 : q < 1) :
    volume (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K k) = 0 := by
  obtain ⟨hcompact, hflatBounded⟩ :=
    SardFlatThroughCompactLocalizationProbe.flatThrough_isCompact_and_bounded
      f K k hK (hf.of_le (by norm_num)) z R hbounded
  exact SardFlatThroughTaylorNullityProbe.flatThrough_image_volume_eq_zero
    f K k hcompact z R hflatBounded d hd hexp hf hk0 hkt q hq0 hq1

#print axioms localized_flatThrough_image_volume_eq_zero
end SardLocalizedFlatThroughTaylorNullityProbe
