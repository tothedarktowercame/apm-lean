import ConstructionTargets.SardProjectedSmoothLocalRankChartSurjectivity

namespace SardLocalizedRankUpperBoundProbe

variable {E F : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- An ambient rank-at-most bound indexed by the exact rank of the base
derivative is the rank bound by the base derivative range itself. -/
theorem finrank_range_le_baseRange_of_le_rankIndex
    (D L : E →ₗ[ℝ] F) (r : ℕ)
    (hbase : Module.finrank ℝ (LinearMap.range L) = r)
    (hrank : Module.finrank ℝ (LinearMap.range D) ≤ r) :
    Module.finrank ℝ (LinearMap.range D) ≤
      Module.finrank ℝ (LinearMap.range L) := by
  simpa [hbase] using hrank

#print axioms finrank_range_le_baseRange_of_le_rankIndex

end SardLocalizedRankUpperBoundProbe
