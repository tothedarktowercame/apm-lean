import ConstructionTargets.SardFirstDerivativeRankPiecePointwiseCompactNullity
import ConstructionTargets.SardFirstDerivativeRankPieceProjectedChart

open Set MeasureTheory

namespace SardFirstDerivativeRankPieceProjectedChartNullityWitnessProbe

/-- Compact nullity certified on the projected chart supplied at each point
aggregates over the complete exact-rank piece. -/
theorem rankPiece_image_null_of_projectedChart_compact_null
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (r : ℕ) (hf : ContDiff ℝ 1 f)
    (hchart : ∀ x, x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r →
      ∀ (U : Set E), IsOpen U → x ∈ U →
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) =
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r}) →
      ∀ e : OpenPartialHomeomorph E
          ((LinearMap.range (fderiv ℝ f x).toLinearMap) ×
            ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
              (fderiv ℝ f x)).ker),
        x ∈ e.source → ∀ C : Set E, IsCompact C →
          C ⊆ {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ U →
          μ (f '' C) = 0) :
    μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)) = 0 := by
  apply SardFirstDerivativeRankPiecePointwiseCompactNullityProbe.rankPiece_image_null_of_pointwise_compact_rankUpper_image_null
    μ f K r hf
  intro x hx
  obtain ⟨U, hU, hxU, hEq, e, hxe⟩ :=
    SardFirstDerivativeRankPieceProjectedChartProbe.exists_open_rankUpperLocus_and_projected_localRankNormalForm
      f K x r hf hx
  exact ⟨U, hU, hxU, hchart x hx U hU hxU hEq e hxe⟩

#print axioms rankPiece_image_null_of_projectedChart_compact_null

end SardFirstDerivativeRankPieceProjectedChartNullityWitnessProbe
