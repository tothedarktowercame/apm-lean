import ConstructionTargets.SardRankPieceCompactProjectedChartAggregation
import ConstructionTargets.SardFirstDerivativeLocusRankAggregation

open Set MeasureTheory

namespace SardFirstDerivativeLocusCompactProjectedChartAggregationProbe

/-- Indexed compact projected-chart certificates close the complete order-one
first-nonzero-derivative locus after finite exact-rank aggregation. -/
theorem firstNonzeroJetLocus_one_image_null_of_compact_projectedChart_certificates
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (hf : ContDiff ℝ 1 f)
    (hcritical :
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ⊆
        criticalSet (fun x => (fderiv ℝ f x).toLinearMap))
    (hcompact : ∀ r : Fin (Module.finrank ℝ F), ∀ x, x ∈
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
    μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1) = 0 := by
  apply SardFirstDerivativeLocusRankAggregationProbe.firstNonzeroJetLocus_one_image_null_of_rankStrata
    μ f K hcritical
  intro r
  exact SardRankPieceCompactProjectedChartAggregationProbe.rankPiece_image_null_of_compact_projectedChart_certificates
    μ f K r hf (hcompact r)

#print axioms firstNonzeroJetLocus_one_image_null_of_compact_projectedChart_certificates

end SardFirstDerivativeLocusCompactProjectedChartAggregationProbe
