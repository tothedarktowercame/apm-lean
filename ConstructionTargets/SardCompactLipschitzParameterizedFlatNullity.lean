import ConstructionTargets.SardLipschitzParameterizedFlatTaylorRemainder
import ConstructionTargets.SardQuantitativeTaylorCoverMeasure
import ConstructionTargets.SardArbitrarilySmallMeasureLimit
import ConstructionTargets.SardVolumeNullityToAddHaar

open Metric Set MeasureTheory
open scoped ENNReal NNReal

theorem compact_lipschitz_parameterized_flat_image_addHaar_eq_zero
    {G E F : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [Nontrivial G] [MeasurableSpace G] [BorelSpace G]
    [ProperSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (p : G → E) (s : Set G) (hs : IsCompact s)
    (k : ℕ) (L : ℝ≥0) (hp : LipschitzOnWith L p s)
    (hf : ContDiff ℝ (k + 1) f)
    (hflat : ∀ a ∈ s, ∀ i, 1 ≤ i → i ≤ k →
      iteratedFDeriv ℝ i f (p a) = 0)
    (hdim : Module.finrank ℝ G < (k + 1) * Module.finrank ℝ F) :
    μ ((f ∘ p) '' s) = 0 := by
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall (0 : G)
  have himage : IsCompact (p '' s) := hs.image_of_continuousOn hp.continuousOn
  obtain ⟨T, hT⟩ := himage.isBounded.subset_closedBall (0 : E)
  obtain ⟨C, hC, hrem⟩ := exists_lipschitz_parameterized_flat_taylor_remainder
    f p s 0 T k L hp hT hf hflat
  have hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ G /
      Real.Gamma (Module.finrank ℝ G / 2 + 1)) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply div_pos
    · exact pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _
    · apply Real.Gamma_pos_of_pos
      positivity
  apply SardVolumeNullityToAddHaarProbe.addHaar_eq_zero_of_volume_eq_zero μ
  apply measure_eq_zero_of_le_inv_nat
  intro n
  cases n with
  | zero => simp
  | succ n =>
    obtain ⟨j, centres, _, _, _, _, hvol⟩ := exists_taylor_cover_measure_lt
      (f ∘ p) s hs 0 R C hR hC k
      ((k + 1) * Module.finrank ℝ F - Module.finrank ℝ G)
      (by omega) (by omega) hrem hk0 ENNReal.ofReal_ne_top
      (1 / 2 : ℝ≥0) (by norm_num) (by norm_num)
      (((n + 1 : ℕ) : ENNReal)⁻¹)
      (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _))
    exact hvol.le

#print axioms compact_lipschitz_parameterized_flat_image_addHaar_eq_zero
