import Mathlib

/-!
# APM t96J01 — separation after a compact-to-Hausdorff quotient

The codomain really is the closed interval `[0,1]`, not a real-valued
surrogate with an omitted range condition.
-/

theorem apm_t96j01
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hf_surj : Function.Surjective f)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint (f '' A) (f '' B)) :
    ∃ g : Y → Set.Icc (0 : ℝ) 1,
      Continuous g ∧
      (∀ x ∈ A, g (f x) = ⟨0, by norm_num⟩) ∧
      (∀ x ∈ B, g (f x) = ⟨1, by norm_num⟩) := by
  haveI : CompactSpace Y := ⟨by simpa [hf_surj.range_eq] using isCompact_range hf⟩
  have hA' : IsClosed (f '' A) := (hA.isCompact.image hf).isClosed
  have hB' : IsClosed (f '' B) := (hB.isCompact.image hf).isClosed
  obtain ⟨u, hu0, hu1, hu⟩ := exists_continuous_zero_one_of_isClosed hA' hB' hdisj
  refine ⟨fun y => ⟨u y, hu y⟩, u.continuous.subtype_mk _, ?_, ?_⟩
  · intro x hx; ext; exact hu0 (Set.mem_image_of_mem f hx)
  · intro x hx; ext; exact hu1 (Set.mem_image_of_mem f hx)
