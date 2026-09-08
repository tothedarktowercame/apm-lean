import ConstructionTargets.SardDerivativeRankUpperLocalImageNullity
import ConstructionTargets.SardFirstDerivativeRankPieceLocalNullityAggregation

open Set MeasureTheory

namespace SardFirstDerivativeRankPieceCompactLocalNullityProbe

/-- Compact nullity on local rank-upper neighborhoods aggregates over an exact
rank piece of the order-one locus. -/
theorem rankPiece_image_null_of_locally_compact_rankUpper_image_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (r : ℕ)
    (hf : ContDiff ℝ 1 f) (U : E → Set E)
    (hopen : ∀ x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r, IsOpen (U x))
    (hmem : ∀ x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r, x ∈ U x)
    (hcompact : ∀ x, x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r → ∀ C : Set E, IsCompact C →
      C ⊆ {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ U x →
      μ (f '' C) = 0) :
    μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)) = 0 := by
  apply SardFirstDerivativeRankPieceLocalNullityAggregationProbe.rankPiece_image_null_of_locally_image_null
    μ f K r U hopen hmem
  intro x hx
  apply measure_mono_null (t := f '' ({y |
    Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ U x))
  · apply image_mono
    rintro y ⟨hy, hyU⟩
    exact ⟨by simpa [rankStratum] using hy.2.le, hyU⟩
  · exact SardDerivativeRankUpperLocalImageNullityProbe.measure_image_zero_of_derivativeRankAtMost_inter_open_of_compact
      μ f r (U x) hf (hopen x hx) (hcompact x hx)

#print axioms rankPiece_image_null_of_locally_compact_rankUpper_image_null

end SardFirstDerivativeRankPieceCompactLocalNullityProbe
