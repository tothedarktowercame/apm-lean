import ConstructionTargets.SardFirstNonzeroJetLocusDecomposition
import ConstructionTargets.SardProjectedRangeKernelDimensionDrop

open Set

namespace SardFirstNonzeroJetOneFDerivNonzeroProbe

/-- Membership in the order-one first-nonzero-jet locus makes the ordinary
Fréchet derivative nonzero. -/
theorem fderiv_ne_zero_of_mem_firstNonzeroJetLocus_one
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K : Set E) (x : E)
    (hx : x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1) :
    fderiv ℝ f x ≠ 0 := by
  intro hzero
  apply hx.2.2
  apply norm_eq_zero.mp
  rw [norm_iteratedFDeriv_one, hzero, norm_zero]

#print axioms fderiv_ne_zero_of_mem_firstNonzeroJetLocus_one

end SardFirstNonzeroJetOneFDerivNonzeroProbe
