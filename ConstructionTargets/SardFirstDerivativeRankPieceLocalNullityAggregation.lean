import ConstructionTargets.SardLocalNullitySecondCountableAggregation
import ConstructionTargets.SardFirstDerivativeLocusRankAggregation

open Set MeasureTheory

namespace SardFirstDerivativeRankPieceLocalNullityAggregationProbe

/-- Pointwise local nullity witnesses aggregate over one exact rank piece of
the order-one first-nonzero-derivative locus. -/
theorem rankPiece_image_null_of_locally_image_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (r : ℕ)
    (U : E → Set E)
    (hopen : ∀ x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r,
      IsOpen (U x))
    (hmem : ∀ x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r,
      x ∈ U x)
    (hnull : ∀ x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r,
      μ (f '' ((SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) ∩ U x)) = 0) :
    μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)) = 0 := by
  exact SardLocalNullitySecondCountableAggregationProbe.image_null_of_locally_image_null
    μ f _ U hopen hmem hnull

#print axioms rankPiece_image_null_of_locally_image_null
end SardFirstDerivativeRankPieceLocalNullityAggregationProbe
