import ConstructionTargets.SardLocalizedFiniteJetInductionNullity

open Metric Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace SardFiniteOrderCompactRankZeroInductionNullityProbe
universe u v

theorem compact_rankZero_image_zero_of_finiteJet_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K)
    (hKzero : K ⊆ rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0)
    (z : E) (R : ℝ) (hbounded : K ⊆ closedBall z R)
    (k d : ℕ) (hd : 0 < d)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E + d)
    (hf : ContDiff ℝ (k + 1) f)
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hkt : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ ⊤)
    (q : ℝ≥0) (hq0 : 0 < q) (hq1 : q < 1)
    (n : WithTop ℕ∞) (hn : n ≠ 0)
    (hnTop : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hf1 : ∀ i, 1 ≤ i → i + 1 ≤ k → ContDiff ℝ (i + 1) f)
    (hfn : ∀ i, 1 ≤ i → i + 1 ≤ k → ContDiff ℝ (n + i) f)
    (hindOne : ∀ x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1,
      ∀ (μS : Measure (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ),
        Measure.IsAddHaarMeasure μS →
        ∀ (g : ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
            (fderiv ℝ f x)).ker →
            (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ)
          (s : Set ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
            (fderiv ℝ f x)).ker),
          (∀ y ∈ s, ContDiffAt ℝ 1 g y) →
          μS (g '' (s ∩ {y | ¬ Function.Surjective (fderiv ℝ g y)})) = 0)
    (hindHigher : ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
      [FiniteDimensional ℝ G] [CompleteSpace G],
      Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (g : G → F) (s : Set G),
        (∀ y ∈ s, ContDiffAt ℝ n g y) →
        μF (g '' (s ∩ {y | ¬ Function.Surjective (fderiv ℝ g y)})) = 0) :
    μF (f '' K) = 0 := by
  have hcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y) := by
    intro y hy hsurj
    have hz := hKzero hy
    have htop : LinearMap.range (fderiv ℝ f y).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    change Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) = 0 at hz
    rw [htop, finrank_top] at hz
    exact (Module.finrank_pos (R := ℝ) (M := F)).ne' hz
  apply SardLocalizedFiniteJetInductionNullityProbe.localized_image_zero_of_finiteJet_induction
    μF f K hK z R hbounded k d hd hexp hf hk0 hkt q hq0 hq1 n hn hnTop hf1 hfn
  · intro x hx
    exact hcrit x hx.1
  · exact hindOne
  · exact hindHigher
  · exact hcrit

#print axioms compact_rankZero_image_zero_of_finiteJet_induction
end SardFiniteOrderCompactRankZeroInductionNullityProbe
