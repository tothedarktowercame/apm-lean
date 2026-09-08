import ConstructionTargets.SardFirstDerivativeRankPieceChartSourceCompactNullity
import ConstructionTargets.SardCompactProjectedChartNullityOfResidualData

open Set MeasureTheory

namespace SardRankPieceCompactProjectedChartAggregationProbe

/-- Compact projected-chart nullity certificates on every chart-source
refinement aggregate over the complete exact derivative-rank piece. -/
theorem rankPiece_image_null_of_compact_projectedChart_certificates
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (r : ℕ) (hf : ContDiff ℝ 1 f)
    (hcompact : ∀ x, x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r →
      ∀ chart : OpenPartialHomeomorph E
          ((LinearMap.range (fderiv ℝ f x).toLinearMap) ×
            ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
              (fderiv ℝ f x)).ker),
      ∀ V : Set E, IsOpen V → x ∈ V → V ⊆ chart.source →
        ∀ C : Set E, IsCompact C →
          C ⊆ {y | Module.finrank ℝ
            (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ V →
          μ (f '' C) = 0) :
    μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)) = 0 := by
  exact SardFirstDerivativeRankPieceChartSourceCompactNullityProbe.rankPiece_image_null_of_chartSource_compact_null
    μ f K r hf hcompact

#print axioms rankPiece_image_null_of_compact_projectedChart_certificates

end SardRankPieceCompactProjectedChartAggregationProbe
