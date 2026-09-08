import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
namespace SardProjectedRankReducedDimensionIdentitiesProbe

theorem projected_rank_reduced_finranks
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (r : ℕ)
    (hrank : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r) :
    Module.finrank ℝ
        ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker =
        Module.finrank ℝ E - r ∧
      Module.finrank ℝ (LinearMap.range L.toLinearMap)ᗮ =
        Module.finrank ℝ F - r := by
  let R := LinearMap.range L.toLinearMap
  let A : E →L[ℝ] R := R.orthogonalProjection.comp L
  have hA : A.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    rcases y.property with ⟨z, hz⟩
    refine ⟨z, Subtype.ext ?_⟩
    have hp : R.orthogonalProjection (L z) = y := by
      rw [show L z = (y : F) from hz]
      exact R.orthogonalProjection_mem_subspace_eq_self y
    exact congrArg Subtype.val hp
  have hker := A.toLinearMap.finrank_range_add_finrank_ker
  have hrangeA : Module.finrank ℝ (LinearMap.range A.toLinearMap) = r := by
    rw [show LinearMap.range A.toLinearMap = A.range from rfl, hA]
    simpa using hrank
  have hortho := R.finrank_add_finrank_orthogonal
  change Module.finrank ℝ R = r at hrank
  change Module.finrank ℝ A.ker = Module.finrank ℝ E - r ∧
    Module.finrank ℝ Rᗮ = Module.finrank ℝ F - r
  rw [hrangeA] at hker
  rw [hrank] at hortho
  omega

#print axioms projected_rank_reduced_finranks

end SardProjectedRankReducedDimensionIdentitiesProbe
