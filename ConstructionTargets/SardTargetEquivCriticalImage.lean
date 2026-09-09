import ConstructionTargets.SardSourceEquivCriticalImage

open Set

theorem criticalImage_eq_of_target_continuousLinearEquiv
    {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e : F ≃L[ℝ] H) (f : E → F) (s : Set E)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    (e ∘ f) '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ (e ∘ f) x)}) =
      e '' (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) := by
  have hcrit (x : E) (hx : x ∈ s) :
      (¬ Function.Surjective (fderiv ℝ (e ∘ f) x)) ↔
        ¬ Function.Surjective (fderiv ℝ f x) := by
    have hd := (e.hasFDerivAt.comp x (hf x hx).hasFDerivAt).fderiv
    rw [hd]
    constructor
    · intro hn hs
      apply hn
      intro y
      obtain ⟨z, hz⟩ := hs (e.symm y)
      exact ⟨z, by simpa using congrArg e hz⟩
    · intro hn hs
      apply hn
      intro y
      obtain ⟨z, hz⟩ := hs (e y)
      exact ⟨z, e.injective hz⟩
  apply Set.Subset.antisymm
  · rintro y ⟨x, ⟨hx, hc⟩, rfl⟩
    exact ⟨f x, ⟨x, ⟨hx, (hcrit x hx).1 hc⟩, rfl⟩, rfl⟩
  · rintro y ⟨z, ⟨x, ⟨hx, hc⟩, rfl⟩, rfl⟩
    exact ⟨x, ⟨hx, (hcrit x hx).2 hc⟩, rfl⟩

#print axioms criticalImage_eq_of_target_continuousLinearEquiv
