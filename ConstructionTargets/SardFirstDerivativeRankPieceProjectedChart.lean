import ConstructionTargets.SardFirstDerivativeLocusRankAggregation
import ConstructionTargets.SardExactRankLocalUpperLocus
import ConstructionTargets.SardProjectedImplicitFunctionPackaging

open Set

namespace SardFirstDerivativeRankPieceProjectedChartProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A point of a localized order-one exact-rank piece has both its open
rank-at-most representation and the projected local rank chart based on the
same derivative. -/
theorem exists_open_rankUpperLocus_and_projected_localRankNormalForm
    (f : E → F) (K : Set E) (x : E) (r : ℕ) (hf : ContDiff ℝ 1 f)
    (hx : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) =
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r}) ∧
      ∃ e : OpenPartialHomeomorph E
          ((LinearMap.range (fderiv ℝ f x).toLinearMap) ×
            ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
              (fderiv ℝ f x)).ker),
        x ∈ e.source := by
  obtain ⟨U, hU, hxU, hRankEq⟩ :=
    exists_open_inter_rankStratum_eq_rankLE f x r hf hx.2
  have hEq :
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) =
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r}) := by
    simpa [inter_assoc, inter_left_comm, inter_comm] using
      congrArg (fun S =>
        SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩ S) hRankEq
  obtain ⟨e, hxe⟩ :=
    SardProjectedImplicitFunctionPackagingProbe.exists_projected_localRankNormalForm
      f x (fderiv ℝ f x) (hf.hasStrictFDerivAt one_ne_zero)
  exact ⟨U, hU, hxU, hEq, e, hxe⟩

#print axioms exists_open_rankUpperLocus_and_projected_localRankNormalForm

end SardFirstDerivativeRankPieceProjectedChartProbe
