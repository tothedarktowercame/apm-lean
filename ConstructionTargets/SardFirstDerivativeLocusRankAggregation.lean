import ConstructionTargets.SardFirstNonzeroJetLocusDecomposition
import ConstructionTargets.SardCriticalRankStrata

open Set MeasureTheory

namespace SardFirstDerivativeLocusRankAggregationProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Localized nullity of every exact derivative-rank stratum aggregates to
nullity of the order-one first-nonzero-jet locus. -/
theorem firstNonzeroJetLocus_one_image_null_of_rankStrata
    [MeasurableSpace F] (μ : Measure F) (f : E → F) (K : Set E)
    (hcritical :
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ⊆
        criticalSet (fun x => (fderiv ℝ f x).toLinearMap))
    (hnull : ∀ r : Fin (Module.finrank ℝ F),
      μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun x => (fderiv ℝ f x).toLinearMap) r)) = 0) :
    μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1) = 0 := by
  let L := SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1
  let f' : E → E →ₗ[ℝ] F := fun x => (fderiv ℝ f x).toLinearMap
  have hdecomp : L = ⋃ r : Fin (Module.finrank ℝ F), L ∩ rankStratum f' r := by
    rw [← inter_iUnion, ← criticalSet_eq_iUnion_rankStratum]
    exact (inter_eq_left.mpr hcritical).symm
  change μ (f '' L) = 0
  rw [hdecomp, image_iUnion]
  change ∀ r : Fin (Module.finrank ℝ F), μ (f '' (L ∩ rankStratum f' r)) = 0 at hnull
  exact measure_iUnion_null hnull

#print axioms firstNonzeroJetLocus_one_image_null_of_rankStrata

end SardFirstDerivativeLocusRankAggregationProbe
