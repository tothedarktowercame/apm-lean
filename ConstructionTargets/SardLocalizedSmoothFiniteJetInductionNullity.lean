import ConstructionTargets.SardLocalizedFiniteJetInductionNullity

open Metric Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace SardLocalizedSmoothFiniteJetInductionNullityProbe

universe u v

theorem localized_image_zero_of_smooth_finiteJet_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K) (z : E) (R : ℝ)
    (hbounded : K ⊆ closedBall z R) (k d : ℕ) (hd : 0 < d)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E + d)
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
  have hcoef : 0 < √Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1) := by positivity
  apply SardLocalizedFiniteJetInductionNullityProbe.localized_image_zero_of_finiteJet_induction
    μF f K hK z R hbounded k d hd hexp (hf.of_le le_top)
    (ENNReal.ofReal_ne_zero_iff.mpr hcoef) ENNReal.ofReal_ne_top
    (1 / 2) (by norm_num) (by norm_num) n hn hnTop
  · intro i hi hik
    exact hf.of_le le_top
  · intro i hi hik
    exact hf.of_le le_top
  · exact hcritical
  · exact hindOne
  · exact hindHigher
  · exact hKcrit

#print axioms localized_image_zero_of_smooth_finiteJet_induction

end SardLocalizedSmoothFiniteJetInductionNullityProbe
