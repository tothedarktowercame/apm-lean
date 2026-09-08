import ConstructionTargets.SardLocalizedSmoothFiniteJetInductionNullity
import ConstructionTargets.SardTaylorExponentSurplus

open Metric Set MeasureTheory

noncomputable section
namespace SardCompactSmoothInductionNullityProbe

universe u v

theorem compact_image_zero_of_smooth_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K)
    (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f)
    (n : WithTop ℕ∞) (hn : n ≠ 0)
    (hnTop : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hcritical :
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ⊆
        criticalSet (fun x => (fderiv ℝ f x).toLinearMap))
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
        μF (g '' (s ∩ {y | ¬ Function.Surjective (fderiv ℝ g y)})) = 0)
    (hKcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y)) :
    μF (f '' K) = 0 := by
  obtain ⟨k, d, hd, hexp⟩ :=
    SardTaylorExponentSurplusProbe.exists_taylor_exponent_surplus (E := E) (F := F)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  exact SardLocalizedSmoothFiniteJetInductionNullityProbe.localized_image_zero_of_smooth_finiteJet_induction
    μF f K hK 0 R hR k d hd hexp hf n hn hnTop hcritical
      hindOne hindHigher hKcrit

#print axioms compact_image_zero_of_smooth_induction

end SardCompactSmoothInductionNullityProbe
