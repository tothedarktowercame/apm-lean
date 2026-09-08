import ConstructionTargets.SardDerivativeRankUpperLocusClosed

open Set

namespace SardDerivativeRankUpperCompactExhaustionProbe

/-- The derivative rank-at-most locus of a C¹ map has an explicit compact
exhaustion when the source is sigma-compact. -/
theorem exists_compact_cover_derivativeRankAtMost
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SigmaCompactSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E → F) (r : ℕ) (hf : ContDiff ℝ 1 f) :
    ∃ K : ℕ → Set E, (∀ n, IsCompact (K n)) ∧
      ⋃ n, K n = {x | Module.finrank ℝ
        (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r} := by
  apply SardClosedSetCompactExhaustionProbe.exists_countable_compact_cover_of_isClosed
  exact SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost f r hf

#print axioms exists_compact_cover_derivativeRankAtMost

end SardDerivativeRankUpperCompactExhaustionProbe
