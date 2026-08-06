import Mathlib

/-! # APM t95J01: Hausdorffness under a perfect surjection

## Statement repairs

The phrase “`π⁻¹` is compact for all `y`” is read as “the fiber
`π⁻¹({y})` is compact for every `y`”; an inverse map need not exist.
-/

open Set

theorem apm_t95j01
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (π : X → Y) (hcont : Continuous π) (hsurj : Function.Surjective π)
    (hclosed : IsClosedMap π)
    (hcompact : ∀ y : Y, IsCompact (π ⁻¹' ({y} : Set Y))) :
    T2Space Y := by
  constructor
  intro y₁ y₂ hy
  have hfibers : Disjoint (π ⁻¹' ({y₁} : Set Y)) (π ⁻¹' ({y₂} : Set Y)) := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    exact hy (hx₁.symm.trans hx₂)
  obtain ⟨U, V, hU, hV, hfiberU, hfiberV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hcompact y₁) (hcompact y₂) hfibers
  let W₁ : Set Y := (π '' Uᶜ)ᶜ
  let W₂ : Set Y := (π '' Vᶜ)ᶜ
  have hW₁ : IsOpen W₁ := (hclosed Uᶜ hU.isClosed_compl).isOpen_compl
  have hW₂ : IsOpen W₂ := (hclosed Vᶜ hV.isClosed_compl).isOpen_compl
  have hy₁W₁ : y₁ ∈ W₁ := by
    intro hy₁
    obtain ⟨x, hxU, hxy⟩ := hy₁
    exact hxU (hfiberU hxy)
  have hy₂W₂ : y₂ ∈ W₂ := by
    intro hy₂
    obtain ⟨x, hxV, hxy⟩ := hy₂
    exact hxV (hfiberV hxy)
  have hW : Disjoint W₁ W₂ := by
    rw [Set.disjoint_left]
    intro y hyW₁ hyW₂
    obtain ⟨x, rfl⟩ := hsurj y
    apply hUV.le_bot
    refine ⟨?_, ?_⟩
    · by_contra hxU
      exact hyW₁ ⟨x, hxU, rfl⟩
    · by_contra hxV
      exact hyW₂ ⟨x, hxV, rfl⟩
  exact ⟨W₁, W₂, hW₁, hW₂, hy₁W₁, hy₂W₂, hW⟩
