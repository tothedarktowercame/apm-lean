import ConstructionTargets.SardClosedSetCompactExhaustion
import ConstructionTargets.SardExactRankLocalUpperLocus

open Set

namespace SardDerivativeRankUpperLocusClosedProbe

/-- For a C¹ map between finite-dimensional real normed spaces, the locus
where derivative rank is at most `r` is closed. -/
theorem isClosed_derivativeRankAtMost
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E → F) (r : ℕ) (hf : ContDiff ℝ 1 f) :
    IsClosed {x | Module.finrank ℝ
      (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r} := by
  rw [← isOpen_compl_iff]
  convert isOpen_derivativeRankAtLeast f (r + 1) hf using 1
  ext x
  simp only [mem_compl_iff, mem_setOf_eq, derivativeRankAtLeast]
  change ¬ Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r ↔
    ((r + 1 : ℕ) : Cardinal) ≤ Module.rank ℝ
      (LinearMap.range (fderiv ℝ f x).toLinearMap)
  rw [← Submodule.finrank_eq_rank]
  norm_cast
  omega

#print axioms isClosed_derivativeRankAtMost

end SardDerivativeRankUpperLocusClosedProbe
