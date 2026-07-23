import Mathlib
import ApmCanaries.Frames.M96J01.Apm_v2_m96J01_1775007086632.Scratch

noncomputable section
open scoped RealInnerProductSpace

namespace ApmCanaries.Frames.M96J01.Apm_v2_m96J01_1775007086632.Main

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The orthogonal projection onto a closed subspace `V` viewed as an endomorphism of `H`. -/
def proj (V : ClosedSubmodule ℝ H) : H →L[ℝ] H :=
  (V : Submodule ℝ H).starProjection

@[simp] lemma proj_apply (V : ClosedSubmodule ℝ H) (x : H) : proj V x =
    (V : Submodule ℝ H).starProjection x := rfl

lemma proj_linear (V : ClosedSubmodule ℝ H) :
    (proj V 0 = 0) ∧ (∀ x y, proj V (x + y) = proj V x + proj V y) ∧
      (∀ r : ℝ, ∀ x, proj V (r • x) = r • proj V x) := by
  constructor
  · simp [proj]
  · constructor
    · intro x y; simpa [proj] using (proj V).map_add x y
    · intro r x; simpa [proj] using (proj V).map_smulₛₗ r x

lemma proj_norm_one (V : ClosedSubmodule ℝ H)
    (hV : (V : Submodule ℝ H) ≠ ⊥) : ‖proj V‖ = 1 := by
  simpa [proj] using Submodule.norm_starProjection (K := (V : Submodule ℝ H)) hV

lemma proj_isSelfAdjoint (V : ClosedSubmodule ℝ H) : IsSelfAdjoint (proj V) := by
  simpa [proj] using isSelfAdjoint_starProjection (V : Submodule ℝ H)

lemma proj_idempotent (V : ClosedSubmodule ℝ H) :
    (proj V).comp (proj V) = proj V := by
  ext x
  have hx : proj V x ∈ (V : Submodule ℝ H) := by
    simpa [proj] using (Submodule.starProjection_apply_mem (V := (V : Submodule ℝ H)) x)
  have := (Submodule.starProjection_eq_self_iff (K := (V : Submodule ℝ H)) (v := proj V x)).2 hx
  simpa [proj] using this

/-- Bundled version of the four properties required in the problem statement. -/
theorem projection_properties
    (V : ClosedSubmodule ℝ H) (hV : (V : Submodule ℝ H) ≠ ⊥) :
    let F := proj V in
    (F 0 = 0 ∧ ∀ x y, F (x + y) = F x + F y ∧ ∀ r : ℝ, F (r • x) = r • F x) ∧
    ‖F‖ = 1 ∧ IsSelfAdjoint F ∧ F.comp F = F := by
  intro F
  refine ⟨?_, proj_norm_one V hV, proj_isSelfAdjoint V, proj_idempotent V⟩
  constructor
  · simpa [proj]
  · constructor
    · intro x y; simpa [proj] using (proj V).map_add x y
    · intro r x; simpa [proj] using (proj V).map_smulₛₗ r x

end ApmCanaries.Frames.M96J01.Apm_v2_m96J01_1775007086632.Main
