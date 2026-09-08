import ConstructionTargets.SardCompactSmoothInductionNullity
import ConstructionTargets.SardSmoothCriticalLocusCompactExhaustionNullity

open Set MeasureTheory

noncomputable section
namespace SardSmoothCriticalImageInductionAssemblyProbe

universe u v

theorem smooth_criticalImage_zero_of_induction_interfaces
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    [SecondCountableTopology E] [SigmaCompactSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f)
    (n : WithTop ℕ∞) (hn : n ≠ 0)
    (hnTop : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hcritical : ∀ K : Set E,
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ⊆
        criticalSet (fun x => (fderiv ℝ f x).toLinearMap))
    (hindOne : ∀ (K : Set E) x, x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 →
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
    μF (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply SardSmoothCriticalLocusCompactExhaustionNullityProbe.smooth_criticalLocus_image_zero_of_compact_induction
    μF f hf
  intro K hK hKcrit
  apply SardCompactSmoothInductionNullityProbe.compact_image_zero_of_smooth_induction
    μF f K hK hf n hn hnTop (hcritical K) (hindOne K) hindHigher
  exact fun y hy => hKcrit hy

#print axioms smooth_criticalImage_zero_of_induction_interfaces

end SardSmoothCriticalImageInductionAssemblyProbe
