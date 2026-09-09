import ConstructionTargets.SardCompactFlatEndpointNormalizedNullity
import ConstructionTargets.SardFlatThroughCompactLocalization
import ConstructionTargets.SardVolumeNullityToAddHaar

open Metric Set MeasureTheory
open scoped ENNReal NNReal

theorem localized_flatThrough_endpoint_image_addHaar_eq_zero
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E) :
    μF (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K (k + 1)) = 0 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  have hflat := (SardFlatThroughCompactLocalizationProbe.flatThrough_isCompact_and_bounded
    f K (k + 1) hK hf 0 R hR).1
  apply SardVolumeNullityToAddHaarProbe.addHaar_eq_zero_of_volume_eq_zero
  apply compact_flat_endpoint_volume_eq_zero_normalized f _ hflat k hf
  · intro a ha i hi hik
    exact ha.2 i hi hik
  · exact hexp

#print axioms localized_flatThrough_endpoint_image_addHaar_eq_zero
