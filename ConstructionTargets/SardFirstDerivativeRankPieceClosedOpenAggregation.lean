import ConstructionTargets.SardFirstDerivativeRankPiecePointwiseClosedOpenNullity
import ConstructionTargets.SardFirstDerivativeRankPieceLocalNullityAggregation

open Set MeasureTheory

noncomputable section

namespace SardFirstDerivativeRankPieceClosedOpenAggregationProbe

/-- Pointwise closed-rank-locus null neighborhoods aggregate to nullity of one
order-one exact derivative-rank piece. -/
theorem rankPiece_image_zero_of_pointwise_closedOpen
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (K : Set E) (r : ℕ) (hf : ContDiff ℝ 1 f)
    (hcrit : ∀ x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r,
      ¬ Function.Surjective (fderiv ℝ f x))
    (hind : ∀ x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r,
      ∀ (μS : Measure (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ),
        Measure.IsAddHaarMeasure μS →
        ∀ (q : ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
            (fderiv ℝ f x)).ker →
            (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ)
          (u : Set ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
            (fderiv ℝ f x)).ker),
          (∀ z ∈ u, ContDiffAt ℝ 1 q z) →
          μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) :
    μF (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
      rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)) = 0 := by
  classical
  let S := SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
    rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r
  have hex : ∀ x ∈ S, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      μF (f '' ({y | Module.finrank ℝ
        (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ U)) = 0 := by
    intro x hx
    exact SardFirstDerivativeRankPiecePointwiseClosedOpenNullityProbe.exists_open_rankUpper_image_zero
      μF f K r hf x hx.1 hx.2 (hcrit x hx) (hind x hx)
  let U : E → Set E := fun x =>
    if hx : x ∈ S then Classical.choose (hex x hx) else ∅
  have hopen : ∀ x ∈ S, IsOpen (U x) := by
    intro x hx
    simp only [U, dif_pos hx]
    exact (Classical.choose_spec (hex x hx)).1
  have hmem : ∀ x ∈ S, x ∈ U x := by
    intro x hx
    simp only [U, dif_pos hx]
    exact (Classical.choose_spec (hex x hx)).2.1
  have hnull : ∀ x ∈ S, μF (f '' ({y | Module.finrank ℝ
      (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ U x)) = 0 := by
    intro x hx
    simp only [U, dif_pos hx]
    exact (Classical.choose_spec (hex x hx)).2.2
  apply SardFirstDerivativeRankPieceLocalNullityAggregationProbe.rankPiece_image_null_of_locally_image_null
    μF f K r U hopen hmem
  intro x hx
  apply measure_mono_null _ (hnull x hx)
  rintro y ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.1.2.le, hz.2⟩, rfl⟩

#print axioms rankPiece_image_zero_of_pointwise_closedOpen

end SardFirstDerivativeRankPieceClosedOpenAggregationProbe
