import ConstructionTargets.SardFirstDerivativeLocusClosedOpenFiniteAggregation
import ConstructionTargets.SardFirstNonzeroJetFiniteAssembly

open Set MeasureTheory

noncomputable section

namespace SardLocalizedFiniteJetClosedOpenAssemblyProbe

/-- Taylor-flat nullity, higher-jet induction, and the closed-open order-one
rank argument assemble to nullity of a complete localized source set. -/
theorem image_zero_of_flat_higher_and_closedOpen_first
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (K : Set E) (k : ℕ) (hf : ContDiff ℝ 1 f)
    (hcritical :
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ⊆
        criticalSet (fun x => (fderiv ℝ f x).toLinearMap))
    (hind : ∀ x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1,
      ∀ (μS : Measure (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ),
        Measure.IsAddHaarMeasure μS →
        ∀ (q : ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
            (fderiv ℝ f x)).ker →
            (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ)
          (u : Set ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
            (fderiv ℝ f x)).ker),
          (∀ z ∈ u, ContDiffAt ℝ 1 q z) →
          μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (hflat : μF (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K k) = 0)
    (hhigher : ∀ i ∈ Set.Icc 2 k,
      μF (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
        f K i) = 0) :
    μF (f '' K) = 0 := by
  apply SardFirstNonzeroJetFiniteAssemblyProbe.image_null_of_flat_first_and_higher_firstNonzeroJetLoci
    μF f K k hflat
  · exact SardFirstDerivativeLocusClosedOpenFiniteAggregationProbe.firstNonzeroJetLocus_one_image_zero_of_closedOpen_rankPieces
      μF f K hf hcritical hind
  · exact hhigher

#print axioms image_zero_of_flat_higher_and_closedOpen_first

end SardLocalizedFiniteJetClosedOpenAssemblyProbe
