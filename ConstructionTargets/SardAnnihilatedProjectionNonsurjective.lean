import Mathlib

namespace SardAnnihilatedProjectionNonsurjectiveProbe

variable {E F R : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup R] [Module ℝ R] [Nontrivial R]

/-- A linear map cannot be surjective when a surjective projection to a
nontrivial space annihilates its entire range. -/
theorem LinearMap.not_surjective_of_surjective_comp_eq_zero
    (L : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] R)
    (hP : Function.Surjective P) (hzero : P.comp L = 0) :
    ¬ Function.Surjective L := by
  intro hL
  have hcomp : Function.Surjective (P.comp L) := hP.comp hL
  rw [hzero] at hcomp
  obtain ⟨r, hr⟩ := exists_ne (0 : R)
  obtain ⟨x, hx⟩ := hcomp r
  simpa using hr (hx ▸ rfl)

#print axioms LinearMap.not_surjective_of_surjective_comp_eq_zero
end SardAnnihilatedProjectionNonsurjectiveProbe
