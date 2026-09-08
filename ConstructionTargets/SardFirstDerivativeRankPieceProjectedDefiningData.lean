import ConstructionTargets.SardFirstDerivativeLocusRankAggregation
import ConstructionTargets.SardExactRankLocalUpperLocus
import ConstructionTargets.SardProjectedComplementedStrictDerivativeData
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Set
noncomputable section

namespace SardFirstDerivativeRankPieceImplicitFunctionDataProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

local instance derivativeRangeCompleteSpace (L : E →L[ℝ] F) :
    CompleteSpace (LinearMap.range L.toLinearMap) := by
  letI := L.toLinearMap.finiteDimensional_range
  exact (LinearMap.range L.toLinearMap).complete_of_finiteDimensional.completeSpace_coe

/-- The localized rank-at-most neighborhood and every defining field needed
for the exact projected `ImplicitFunctionData` at the same exact-rank point. -/
theorem exists_open_rankUpperLocus_and_projected_definingData
    (f : E → F) (K : Set E) (x : E) (r : ℕ) (hf : ContDiff ℝ 1 f)
    (hx : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) =
      U ∩ (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r}) ∧
      let L := fderiv ℝ f x
      let R := LinearMap.range L.toLinearMap
      let A : E →L[ℝ] R := R.orthogonalProjection.comp L
      let G := A.ker
      let B : E →L[ℝ] G := G.orthogonalProjection
      HasStrictFDerivAt (fun y => R.orthogonalProjection (f y)) A x ∧
        HasStrictFDerivAt (fun y => G.orthogonalProjection y) B x ∧
        A.range = ⊤ ∧ B.range = ⊤ ∧ IsCompl A.ker B.ker := by
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
  refine ⟨U, hU, hxU, hEq, ?_⟩
  dsimp only
  let L := fderiv ℝ f x
  let R := LinearMap.range L.toLinearMap
  let A : E →L[ℝ] R := R.orthogonalProjection.comp L
  let G := A.ker
  let B : E →L[ℝ] G := G.orthogonalProjection
  exact SardProjectedImplicitFunctionDataProbe.projected_complemented_strictDerivative_data
    f x L (hf.hasStrictFDerivAt one_ne_zero)

#print axioms exists_open_rankUpperLocus_and_projected_definingData

end SardFirstDerivativeRankPieceImplicitFunctionDataProbe
