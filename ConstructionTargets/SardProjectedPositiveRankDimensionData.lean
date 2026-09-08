import ConstructionTargets.SardProjectedRankReducedDimensionIdentities

noncomputable section
namespace SardProjectedPositiveRankDimensionDataProbe

theorem projected_positiveRank_dimension_data
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (r : ℕ)
    (hrank : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hrpos : 0 < r) :
    r ≤ Module.finrank ℝ E ∧
      r ≤ Module.finrank ℝ F ∧
      Module.finrank ℝ
        ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker <
        Module.finrank ℝ E := by
  have hdims :=
    SardProjectedRankReducedDimensionIdentitiesProbe.projected_rank_reduced_finranks L r hrank
  have hrSource : r ≤ Module.finrank ℝ E := by
    have h := L.toLinearMap.finrank_range_add_finrank_ker
    rw [hrank] at h
    omega
  have hrTarget : r ≤ Module.finrank ℝ F := by
    rw [← hrank]
    exact Submodule.finrank_le _
  exact ⟨hrSource, hrTarget, by rw [hdims.1]; omega⟩

#print axioms projected_positiveRank_dimension_data

end SardProjectedPositiveRankDimensionDataProbe
