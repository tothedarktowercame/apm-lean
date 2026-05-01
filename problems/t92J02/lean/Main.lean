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
    [T2Space Y] {f : X → Y}
    (hcompact : IsCompact (Set.univ : Set X)) (hf : Continuous f)
    (hbij : Function.Bijective f) :
    ∃ h : X ≃ₜ Y, h.toContinuousMap = ⟨f, hf⟩ := by
  classical
  -- Equip X with the compact-space structure coming from `hcompact`.
  haveI : CompactSpace X := ⟨⟨by simpa using hcompact⟩⟩
  -- Continuous images of closed sets are compact and hence closed in a Hausdorff space.
  have hClosedMap : IsClosedMap f := by
    intro C hC
    have hCcompact : IsCompact C := hC.isCompact
    have : IsCompact (f '' C) := hCcompact.image hf
    simpa using this.isClosed
  -- Choose an inverse `g` provided by bijectivity and record its algebraic properties.
  obtain ⟨g, hg₁, hg₂⟩ := hbij.has_inverse
  -- Identify the preimage of a closed set under `g` with the closed image under `f`.
  have hg_preimage_eq : ∀ {C : Set X}, IsClosed C → g ⁻¹' C = f '' C := by
    intro C hC
    ext y; constructor
    · intro hy
      refine ⟨g y, hy, ?_⟩
      simpa using hg₂ y
    · rintro ⟨x, hxC, rfl⟩
      simpa [hg₁ x] using hxC
  -- The inverse map is continuous because it pulls back closed sets to closed sets.
  have hgcont : Continuous g := by
    refine continuous_iff_isClosed_preimage.mpr ?_
    intro C hC
    have hImageClosed : IsClosed (f '' C) := hClosedMap hC
    simpa [hg_preimage_eq hC] using hImageClosed
  -- Package everything into a homeomorphism whose forward map is `f`.
  refine ⟨
    { toEquiv := ⟨f, g, hg₁, hg₂⟩
      continuous_toFun := hf
      continuous_invFun := hgcont },
    rfl⟩

end ApmCanaries.Frames.T92J02.Apm_v2_t92J02_1775008678104.Main
