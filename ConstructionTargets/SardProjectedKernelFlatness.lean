import Mathlib

namespace SardProjectedKernelFlatnessProbe


variable {E F R : Type*}
  [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup R] [Module ℝ R]

/-- A surjective rank-r projection of a map whose full rank is at most r has
the same kernel as the full map. Thus the residual derivative is flat along
the projected coordinate fibre. -/
theorem ker_eq_of_comp_surjective_of_finrank_range_le
    (L : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] R)
    (hsurj : (P.comp L).range = ⊤)
    (hrank : Module.finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ R) :
    LinearMap.ker (P.comp L) = LinearMap.ker L := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · intro v hv
    change P (L v) = 0
    rw [show L v = 0 from hv]
    exact map_zero P
  · have hL := L.finrank_range_add_finrank_ker
    have hPL := (P.comp L).finrank_range_add_finrank_ker
    have hr : Module.finrank ℝ (LinearMap.range (P.comp L)) =
        Module.finrank ℝ R := by rw [hsurj, finrank_top]
    have hcomp_le : Module.finrank ℝ (LinearMap.range (P.comp L)) ≤
        Module.finrank ℝ (LinearMap.range L) := by
      rw [LinearMap.range_comp]
      exact Submodule.finrank_map_le P (LinearMap.range L)
    omega

/-- Pointwise form: every vector tangent to the projected-coordinate fibre is
killed by the full derivative under the same rank bound. -/
theorem apply_eq_zero_of_mem_projected_ker
    (L : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] R)
    (hsurj : (P.comp L).range = ⊤)
    (hrank : Module.finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ R)
    {v : E} (hv : v ∈ LinearMap.ker (P.comp L)) : L v = 0 := by
  have hk := ker_eq_of_comp_surjective_of_finrank_range_le L P hsurj hrank
  exact (show v ∈ LinearMap.ker L from hk ▸ hv)

#print axioms ker_eq_of_comp_surjective_of_finrank_range_le
#print axioms apply_eq_zero_of_mem_projected_ker
end SardProjectedKernelFlatnessProbe
