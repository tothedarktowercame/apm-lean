import ConstructionTargets.SardFirstDerivativeRankPieceCompactLocalNullity

open Set MeasureTheory

namespace SardFirstDerivativeRankPiecePointwiseCompactNullityProbe

/-- Pointwise existence of compact-null rank-upper neighborhoods implies
nullity of the complete exact-rank piece. -/
theorem rankPiece_image_null_of_pointwise_compact_rankUpper_image_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (r : ℕ)
    (hf : ContDiff ℝ 1 f)
    (hlocal : ∀ x, x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r →
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∀ C : Set E, IsCompact C →
        C ⊆ {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ U →
        μ (f '' C) = 0) :
    μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)) = 0 := by
  classical
  let T := SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
    rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r
  let U : E → Set E := fun x => if hx : x ∈ T then Classical.choose (hlocal x hx) else ∅
  apply SardFirstDerivativeRankPieceCompactLocalNullityProbe.rankPiece_image_null_of_locally_compact_rankUpper_image_null
    μ f K r hf U
  · intro x hx
    simpa only [U, T, dif_pos hx] using (Classical.choose_spec (hlocal x hx)).1
  · intro x hx
    simpa only [U, T, dif_pos hx] using (Classical.choose_spec (hlocal x hx)).2.1
  · intro x hx
    simpa only [U, T, dif_pos hx] using (Classical.choose_spec (hlocal x hx)).2.2

#print axioms rankPiece_image_null_of_pointwise_compact_rankUpper_image_null

end SardFirstDerivativeRankPiecePointwiseCompactNullityProbe
