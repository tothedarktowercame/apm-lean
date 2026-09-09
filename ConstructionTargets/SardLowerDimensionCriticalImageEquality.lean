import ConstructionTargets.SardLowerDimensionAmbientImageNullity

open Set

theorem criticalImage_eq_image_of_lower_dimension
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (s : Set E)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F) :
    f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)}) = f '' s := by
  have hcrit : ∀ x, ¬ Function.Surjective (fderiv ℝ f x) := by
    intro x hs
    have hr := LinearMap.finrank_range_le (fderiv ℝ f x).toLinearMap
    rw [LinearMap.range_eq_top.mpr hs] at hr
    simp at hr
    omega
  have heq : s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)} = s := by
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hcrit x⟩⟩
  rw [heq]

#print axioms criticalImage_eq_image_of_lower_dimension
