import ConstructionTargets.SardLocalizedFlatThroughEndpointNullity
import ConstructionTargets.SardLocalizedFlatThroughAddHaarNullity

open Metric Set MeasureTheory
open scoped ENNReal NNReal

theorem compact_flatThrough_image_zero_of_nonnegative_budget
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hbudget : Module.finrank ℝ E ≤ (k + 1) * Module.finrank ℝ F) :
    μF (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K (k + 1)) = 0 := by
  rcases hbudget.eq_or_lt with heq | hlt
  · exact localized_flatThrough_endpoint_image_addHaar_eq_zero μF f K hK k hf heq.symm
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
    have hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
        Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0 := by
      apply ne_of_gt
      apply ENNReal.ofReal_pos.mpr
      apply div_pos
      · exact pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _
      · apply Real.Gamma_pos_of_pos
        positivity
    have hz := SardLocalizedFlatThroughAddHaarNullityProbe.localized_flatThrough_image_addHaar_eq_zero
      μF f K hK 0 R hR k ((k + 1) * Module.finrank ℝ F - Module.finrank ℝ E)
      (Nat.sub_pos_iff_lt.mpr hlt) (by omega) hf hk0 ENNReal.ofReal_ne_top
      (1 / 2) (by norm_num) (by norm_num)
    apply measure_mono_null (image_mono ?_) hz
    intro x hx
    exact ⟨hx.1, fun i hi hik => hx.2 i hi (by omega)⟩

#print axioms compact_flatThrough_image_zero_of_nonnegative_budget
