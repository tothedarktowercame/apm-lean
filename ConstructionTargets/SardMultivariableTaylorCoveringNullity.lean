import ConstructionTargets.SardUniformFlatTaylorRemainder
import ConstructionTargets.SardQuantitativeTaylorCoverMeasure
import ConstructionTargets.SardArbitrarilySmallMeasureLimit

open Metric Set MeasureTheory
open scoped ENNReal NNReal

/-- Smooth flatness on a compact bounded locus supplies the complete
quantitative finite Taylor cover at every positive target-volume tolerance. -/
theorem exists_smooth_flat_taylor_cover_measure_lt
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
    (hzero : ∀ a ∈ K, ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f a = 0)
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hkt : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ ⊤)
    (q : ℝ≥0) (hq0 : 0 < q) (hq1 : q < 1)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (C : ℝ) (j : ℕ) (centres : Finset E),
      0 ≤ C ∧ (↑centres : Set E) ⊆ K ∧
      IsSeparated ((q ^ j : ℝ≥0) : ENNReal) (↑centres : Set E) ∧
      IsCover (q ^ j) K (↑centres : Set E) ∧
      (f '' K ⊆ ⋃ a ∈ centres,
        closedBall (f a) (C * ((q ^ j : ℝ≥0) : ℝ) ^ (k + 1))) ∧
      volume (f '' K) < ε := by
  obtain ⟨C, hC, hrem⟩ :=
    exists_uniform_flat_taylor_remainder_on_bounded_set f K z R k hbounded hf hzero
  obtain ⟨j, centres, hcK, hsep, hcover, himage, hvol⟩ :=
    exists_taylor_cover_measure_lt f K hK z R C hbounded hC k d hd hexp hrem
      hk0 hkt q hq0 hq1 ε hε
  exact ⟨C, j, centres, hC, hcK, hsep, hcover, himage, hvol⟩

/-- Under the positive Morse--Sard exponent surplus, a compact bounded locus
flat through order `k` has target image of zero volume. -/
theorem smooth_flat_locus_image_volume_eq_zero
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
    (hzero : ∀ a ∈ K, ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f a = 0)
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hkt : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ ⊤)
    (q : ℝ≥0) (hq0 : 0 < q) (hq1 : q < 1) :
    volume (f '' K) = 0 := by
  apply measure_eq_zero_of_le_inv_nat volume (f '' K)
  intro n
  cases n with
  | zero => simp
  | succ n =>
      have hε : 0 < ((n + 1 : ℕ) : ENNReal)⁻¹ :=
        ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
      obtain ⟨C, j, centres, hC, hcK, hsep, hcover, himage, hvol⟩ :=
        exists_smooth_flat_taylor_cover_measure_lt f K hK z R hbounded k d hd hexp
          hf hzero hk0 hkt q hq0 hq1 ((n + 1 : ℕ) : ENNReal)⁻¹ hε
      exact hvol.le

#print axioms exists_smooth_flat_taylor_cover_measure_lt
#print axioms smooth_flat_locus_image_volume_eq_zero
