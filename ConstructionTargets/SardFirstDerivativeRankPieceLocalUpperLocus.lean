import ConstructionTargets.SardFirstDerivativeLocusRankAggregation
import ConstructionTargets.SardExactRankLocalUpperLocus

open Set

namespace SardFirstDerivativeRankPieceLocalUpperLocusProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Near a point of a localized order-one exact-rank piece, the exact-rank
condition may be replaced by the upper rank bound while retaining the locus. -/
theorem exists_open_inter_firstNonzeroJetLocus_one_rankStratum_eq_rankLE
    (f : E → F) (K : Set E) (x : E) (r : ℕ) (hf : ContDiff ℝ 1 f)
    (hx : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) =
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r}) := by
  obtain ⟨U, hU, hxU, hEq⟩ := exists_open_inter_rankStratum_eq_rankLE f x r hf hx.2
  refine ⟨U, hU, hxU, ?_⟩
  simpa [inter_assoc, inter_left_comm, inter_comm] using
    congrArg (fun S =>
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩ S) hEq

#print axioms exists_open_inter_firstNonzeroJetLocus_one_rankStratum_eq_rankLE

end SardFirstDerivativeRankPieceLocalUpperLocusProbe
