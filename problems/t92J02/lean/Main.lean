import Mathlib
import ApmCanaries.Frames.T92J02.Apm_v2_t92J02_1775008678104.Scratch

noncomputable section

open scoped Topology

namespace ApmCanaries.Frames.T92J02.Apm_v2_t92J02_1775008678104.Main

/-- Continuous images of compact sets are compact (restated for this frame). -/
theorem image_of_compact_isCompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {f : X → Y}
    (hK : IsCompact K) (hf : Continuous f) :
    IsCompact (f '' K) :=
  hK.image hf

/-- A continuous bijection from a compact space to a Hausdorff space is a homeomorphism. -/
theorem homeomorph_of_compact_to_T2
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hbij : Function.Bijective f) :
    ∃ h : X ≃ₜ Y, ⇑h = f :=
  ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hf, rfl⟩

end ApmCanaries.Frames.T92J02.Apm_v2_t92J02_1775008678104.Main

open ApmCanaries.Frames.T92J02.Apm_v2_t92J02_1775008678104.Main in
/-- Part (a) for any compact subset, which includes a compact space as `Set.univ`; part (b). -/
theorem apm_t92j02 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    (∀ (K : Set X) (f : X → Y), IsCompact K → Continuous f → IsCompact (f '' K)) ∧
    (CompactSpace X → T2Space Y → ∀ f : X → Y, Continuous f → Function.Bijective f →
      ∃ h : X ≃ₜ Y, ⇑h = f) :=
  ⟨fun _ _ hK hf => image_of_compact_isCompact hK hf,
    fun _ _ _ hf hb => homeomorph_of_compact_to_T2 hf hb⟩
