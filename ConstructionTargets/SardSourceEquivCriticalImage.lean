import ConstructionTargets.SardCriticalSetUnderParameterization

open Set

theorem criticalImage_eq_of_source_continuousLinearEquiv
    {E G F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : G ≃L[ℝ] E) (f : E → F) (s : Set E)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    (f ∘ e) '' (e ⁻¹' s ∩ {z | ¬ Function.Surjective (fderiv ℝ (f ∘ e) z)}) =
      f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)}) := by
  have hcrit (z : G) (hz : e z ∈ s) :
      (¬ Function.Surjective (fderiv ℝ (f ∘ e) z)) ↔
        ¬ Function.Surjective (fderiv ℝ f (e z)) := by
    have hd := ((hf (e z) hz).hasFDerivAt.comp z e.hasFDerivAt).fderiv
    rw [hd]
    constructor
    · intro hn hs
      apply hn
      intro y
      obtain ⟨x, hx⟩ := hs y
      exact ⟨e.symm x, by simpa using hx⟩
    · intro hn hs
      apply hn
      intro y
      obtain ⟨x, hx⟩ := hs y
      exact ⟨e x, hx⟩
  apply Set.Subset.antisymm
  · rintro y ⟨z, ⟨hz, hc⟩, rfl⟩
    exact ⟨e z, ⟨hz, (hcrit z hz).1 hc⟩, rfl⟩
  · rintro y ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨e.symm x, ⟨by simpa using hx, ?_⟩, by simp⟩
    exact (hcrit (e.symm x) (by simpa using hx)).2 (by simpa using hc)

#print axioms criticalImage_eq_of_source_continuousLinearEquiv
