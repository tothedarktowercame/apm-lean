import ConstructionTargets.SardOpenChartSourceNeighborhoodRefinement
import ConstructionTargets.SardFirstDerivativeRankPiecePointwiseCompactNullity
import ConstructionTargets.SardFirstDerivativeRankPieceProjectedChart

open Set MeasureTheory

namespace SardFirstDerivativeRankPieceChartSourceCompactNullityProbe

/-- Compact-nullity certificates on chart-source refinements aggregate over
the complete exact-rank piece. -/
theorem rankPiece_image_null_of_chartSource_compact_null
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (r : ℕ) (hf : ContDiff ℝ 1 f)
    (hcert : ∀ x, x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r →
      ∀ e : OpenPartialHomeomorph E
          ((LinearMap.range (fderiv ℝ f x).toLinearMap) ×
            ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
              (fderiv ℝ f x)).ker),
      ∀ V : Set E, IsOpen V → x ∈ V → V ⊆ e.source →
        ∀ C : Set E, IsCompact C →
          C ⊆ {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ V →
          μ (f '' C) = 0) :
    μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)) = 0 := by
  apply SardFirstDerivativeRankPiecePointwiseCompactNullityProbe.rankPiece_image_null_of_pointwise_compact_rankUpper_image_null
    μ f K r hf
  intro x hx
  obtain ⟨U, hU, hxU, hEq, e, hxe⟩ :=
    SardFirstDerivativeRankPieceProjectedChartProbe.exists_open_rankUpperLocus_and_projected_localRankNormalForm
      f K x r hf hx
  obtain ⟨V, hV, hxV, hVe, _⟩ :=
    SardOpenChartSourceNeighborhoodRefinementProbe.exists_open_subset_chartSource_with_inter_eq
      e x U
      (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)
      (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r})
      hU hxU hxe hEq
  exact ⟨V, hV, hxV, hcert x hx e V hV hxV hVe⟩

#print axioms rankPiece_image_null_of_chartSource_compact_null

end SardFirstDerivativeRankPieceChartSourceCompactNullityProbe
