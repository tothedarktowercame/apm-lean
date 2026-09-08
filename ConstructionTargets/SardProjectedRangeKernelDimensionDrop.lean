import ConstructionTargets.SardExactRankProjectedChartCompactNullity

noncomputable section

namespace SardProjectedRangeKernelDimensionDropProbe

/-- A nonzero derivative has a strictly lower-dimensional kernel after
projection onto its range. -/
theorem finrank_ker_rangeProjection_comp_lt
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hL : L ≠ 0) :
    Module.finrank ℝ
        ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker <
      Module.finrank ℝ E := by
  let A : E →L[ℝ] (LinearMap.range L.toLinearMap) :=
    (LinearMap.range L.toLinearMap).orthogonalProjection.comp L
  change Module.finrank ℝ A.ker < Module.finrank ℝ E
  have hA : A ≠ 0 := by
    intro hzero
    apply hL
    ext x
    have hx : A x = 0 := by rw [hzero]; rfl
    have hx' := congrArg Subtype.val hx
    change (LinearMap.range L.toLinearMap).starProjection (L x) = 0 at hx'
    rw [show L x = (⟨L x, ⟨x, rfl⟩⟩ : LinearMap.range L.toLinearMap) from rfl,
      Submodule.starProjection_mem_subspace_eq_self] at hx'
    exact hx'
  have hrange : 0 < Module.finrank ℝ (LinearMap.range A.toLinearMap) := by
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hA
    letI : Nontrivial (LinearMap.range A.toLinearMap) :=
      ⟨⟨⟨A x, ⟨x, rfl⟩⟩, 0, fun h => hx (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  rw [← A.toLinearMap.finrank_range_add_finrank_ker]
  omega

#print axioms finrank_ker_rangeProjection_comp_lt

end SardProjectedRangeKernelDimensionDropProbe
