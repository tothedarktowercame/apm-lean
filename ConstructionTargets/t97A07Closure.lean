import Mathlib

noncomputable section

namespace t97A07Closure

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Surjective continuous linear maps between finite-dimensional real normed spaces form an
open set. -/
theorem isOpen_setOf_surjective_clm [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    IsOpen {L : E →L[ℝ] F | Function.Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L hL
  obtain ⟨R, hR⟩ := L.exists_right_inverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  let Φ : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] F) :=
    (ContinuousLinearMap.compL ℝ F E F).flip R
  have hΦ : Continuous Φ := Φ.continuous
  have hunit : Φ L ∈ {A : F →L[ℝ] F | IsUnit A} := by
    rw [show Φ L = ContinuousLinearMap.id ℝ F by simpa [Φ] using hR]
    exact isUnit_one
  filter_upwards [hΦ.continuousAt (Units.isOpen.mem_nhds hunit)] with L' hL'
  rcases hL' with ⟨u, hu⟩
  intro y
  refine ⟨R ((↑(u⁻¹) : F →L[ℝ] F) y), ?_⟩
  change Φ L' ((↑(u⁻¹) : F →L[ℝ] F) y) = y
  rw [← hu]
  simpa only [← ContinuousLinearMap.comp_apply, ← Units.val_mul] using
    congrArg (fun A : F →L[ℝ] F ↦ A y) (u.mul_inv)

end t97A07Closure

#print axioms t97A07Closure.isOpen_setOf_surjective_clm
