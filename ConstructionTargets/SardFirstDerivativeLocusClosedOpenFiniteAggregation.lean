import ConstructionTargets.SardFirstDerivativeRankPieceClosedOpenAggregation
import ConstructionTargets.SardFirstDerivativeLocusRankAggregation

open Set MeasureTheory

noncomputable section

namespace SardFirstDerivativeLocusClosedOpenFiniteAggregationProbe

/-- Pointwise lower-dimensional induction closes every exact-rank piece and
therefore the complete order-one first-nonzero-jet locus. -/
theorem firstNonzeroJetLocus_one_image_zero_of_closedOpen_rankPieces
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (K : Set E) (hf : ContDiff ℝ 1 f)
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
          μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) :
    μF (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1) = 0 := by
  apply SardFirstDerivativeLocusRankAggregationProbe.firstNonzeroJetLocus_one_image_null_of_rankStrata
    μF f K hcritical
  intro r
  apply SardFirstDerivativeRankPieceClosedOpenAggregationProbe.rankPiece_image_zero_of_pointwise_closedOpen
    μF f K r hf
  · intro x hx
    exact hcritical hx.1
  · intro x hx
    exact hind x hx.1

#print axioms firstNonzeroJetLocus_one_image_zero_of_closedOpen_rankPieces

end SardFirstDerivativeLocusClosedOpenFiniteAggregationProbe
