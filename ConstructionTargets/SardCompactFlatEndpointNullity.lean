import ConstructionTargets.SardCompactUniformSmallTaylorRemainder
import ConstructionTargets.SardLocalEndpointCompactCoverData
import ConstructionTargets.SardNNRealGeometricScaleTolerance

open Metric Set MeasureTheory
open scoped ENNReal NNReal

theorem compact_flat_endpoint_volume_eq_zero
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (z : E) (R : ℝ)
    (hbounded : K ⊆ closedBall z R) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hzero : ∀ a ∈ K, ∀ i, 1 ≤ i → i ≤ k + 1 → iteratedFDeriv ℝ i f a = 0)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E)
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0) :
    volume (f '' K) = 0 := by
  apply endpoint_image_volume_eq_zero_of_localSmallCoefficientCoverData f K R k hexp
  intro ε hε
  let A : ENNReal := ENNReal.ofReal (2 * R + 1) ^ Module.finrank ℝ E
  let B : ENNReal := ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ F /
    Real.Gamma (Module.finrank ℝ F / 2 + 1))
  have hAB : A * B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  obtain ⟨j, hj⟩ := ENNReal.exists_nnreal_geometric_scale_pow_lt
    (A * B) ε (1 / 2) (Module.finrank ℝ F) (by norm_num) (by norm_num)
    Module.finrank_pos hε hAB
  let C : ℝ := ((1 / 2 : ℝ≥0) : ℝ) ^ j
  have hC : 0 < C := pow_pos (by norm_num) _
  obtain ⟨δ, hδ, hrem⟩ := exists_uniform_small_taylor_remainder_on_compact_flat
    f K hK k hf hzero C hC
  apply localEndpoint_coverData_of_compact_remainder f K hK z R C δ k ε
    hbounded hC.le hδ hk0 (fun a ha x _ hx => hrem a ha x hx)
  change (A * ENNReal.ofReal C ^ Module.finrank ℝ F) * B < ε
  simpa only [C, mul_assoc, mul_left_comm, mul_comm] using hj

#print axioms compact_flat_endpoint_volume_eq_zero
