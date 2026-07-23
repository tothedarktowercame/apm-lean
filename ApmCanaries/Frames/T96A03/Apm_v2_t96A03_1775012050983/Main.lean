import Mathlib
import ApmCanaries.Frames.T96A03.Apm_v2_t96A03_1775012050983.Scratch

noncomputable section

open scoped BigOperators

namespace ApmCanaries.Frames.T96A03.Apm_v2_t96A03_1775012050983.Main

/-- The linear map that adds the four coordinates of a vector in `ℤ^4`. -/
def sumLinearMap : (Fin 4 → ℤ) →ₗ[ℤ] ℤ :=
{ toFun := fun v => ∑ i, v i
  map_add' := by
    intro v w
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro z v
    simpa [Finset.mul_sum] using
      (Finset.mul_sum z fun i => v i).symm }

lemma sumLinearMap_apply (v : Fin 4 → ℤ) :
    sumLinearMap v = ∑ i, v i := rfl

lemma sumLinearMap_surjective :
    Function.Surjective sumLinearMap := by
  classical
  intro n
  refine ⟨fun i : Fin 4 => if i = 0 then n else 0, ?_⟩
  have hsucc :
      ∑ i : Fin 3, (if (Fin.succ i : Fin 4) = 0 then n else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    simp [Fin.succ_ne_zero]
  have hzero :
      ∑ i : Fin 4, (if i = 0 then n else 0) = n := by
    simpa [Fin.sum_univ_succ, hsucc]
      using (Fin.sum_univ_succ fun i : Fin 4 => (if i = 0 then n else 0))
  simpa [sumLinearMap_apply, hzero]

end ApmCanaries.Frames.T96A03.Apm_v2_t96A03_1775012050983.Main
