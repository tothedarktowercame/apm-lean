import Mathlib
import ApmCanaries.Frames.M99A04.Apm_v2_m99A04_1775007855572.Scratch

noncomputable section

open scoped Topology

namespace ApmCanaries.Frames.M99A04.Apm_v2_m99A04_1775007855572.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable [CompleteSpace X] [CompleteSpace Y]

theorem extend_uniformContinuous_dense {A : Set X} (hA : Dense A) {f : A → Y}
    (hf : UniformContinuous f) :
    ∃! F : X → Y, Continuous F ∧ ∀ ⦃x⦄ (hx : x ∈ A), F x = f ⟨x, hx⟩ := by
  classical
  refine ⟨hA.extend f, ?_, ?_, ?_⟩
  · have hFuc : UniformContinuous (hA.extend f) := hA.uniformContinuous_extend hf
    refine ⟨hFuc.continuous, ?_⟩
    intro x hx
    simpa using hA.extend_of_ind hf ⟨x, hx⟩
  · intro G hG
    have hEq : ∀ x : A, G x = f x := by
      intro x
      simpa [Subtype.coe_prop] using hG.2 x.property
    have hExt := hA.extend_unique hEq hG.1
    simpa using hExt.symm

end ApmCanaries.Frames.M99A04.Apm_v2_m99A04_1775007855572.Main
