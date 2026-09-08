import ConstructionTargets.SardResidualDerivativeCompositionEqZero
import ConstructionTargets.SardProjectedKernelFlatness

namespace SardRankUpperResidualSliceAnnihilationProbe

variable {E F R G S : Type*}
  [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup R] [Module ℝ R]
  [AddCommGroup G] [Module ℝ G]
  [AddCommGroup S] [Module ℝ S]

/-- A rank-upper derivative annihilates every residual coordinate along slice
directions whose projected derivative vanishes. -/
theorem residual_annihilates_slice_of_rankUpper
    (D : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] R) (Q : F →ₗ[ℝ] S) (J : G →ₗ[ℝ] E)
    (hsurj : (P.comp D).range = ⊤)
    (hrank : Module.finrank ℝ (LinearMap.range D) ≤ Module.finrank ℝ R)
    (hprojected : P.comp (D.comp J) = 0) :
    ∀ v, Q (D (J v)) = 0 := by
  intro v
  have hv : J v ∈ LinearMap.ker (P.comp D) := by
    change P (D (J v)) = 0
    have := LinearMap.congr_fun hprojected v
    exact this
  have hzero := SardProjectedKernelFlatnessProbe.apply_eq_zero_of_mem_projected_ker
    D P hsurj hrank hv
  rw [hzero]
  exact map_zero Q

#print axioms residual_annihilates_slice_of_rankUpper

end SardRankUpperResidualSliceAnnihilationProbe
