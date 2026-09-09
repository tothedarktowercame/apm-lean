import ConstructionTargets.SardCompactFlatEndpointNullity

open Metric Set MeasureTheory
open scoped ENNReal NNReal

theorem compact_flat_endpoint_volume_eq_zero_normalized
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hzero : ∀ a ∈ K, ∀ i, 1 ≤ i → i ≤ k + 1 → iteratedFDeriv ℝ i f a = 0)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E) :
    volume (f '' K) = 0 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  apply compact_flat_endpoint_volume_eq_zero f K hK 0 R hR k hf hzero hexp
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  apply div_pos
  · exact pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _
  · apply Real.Gamma_pos_of_pos
    positivity

#print axioms compact_flat_endpoint_volume_eq_zero_normalized
