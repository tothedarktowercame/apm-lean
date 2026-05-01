import Mathlib
import ApmCanaries.Frames.T92J01.Apm_v2_t92J01_1775008525795.Scratch

noncomputable section

open Set

namespace ApmCanaries.Frames.T92J01.Apm_v2_t92J01_1775008525795.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

variables {A X : Type*} [TopologicalSpace X]

theorem connected_union {C : A → Set X} {x : X}
    (hConn : ∀ a, IsConnected (C a)) (hx : ∀ a, x ∈ C a) :
    IsConnected (⋃ a, C a) := by
  classical
  have hpre : IsPreconnected (⋃ a, C a) := by
    simpa [sUnion_range] using
      (isPreconnected_sUnion x (Set.range C)
        (by rintro s ⟨a, rfl⟩; exact hx a)
        (by rintro s ⟨a, rfl⟩; exact (hConn a).isPreconnected))
  by_cases hnon : (⋃ a, C a).Nonempty
  · exact ⟨hnon, hpre⟩
  · have hUnion : (⋃ a, C a) = (∅ : Set X) := by
      simpa [Set.not_nonempty_iff] using hnon
    simpa [hUnion] using (isConnected_empty : IsConnected (∅ : Set X))

end ApmCanaries.Frames.T92J01.Apm_v2_t92J01_1775008525795.Main
