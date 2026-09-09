import ConstructionTargets.SardSameSpaceAmbientCriticalNullity

open Set MeasureTheory

theorem image_zero_of_lower_dimension_surjective_lift
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (p : F →L[ℝ] E) (hp : Function.Surjective p)
    (f : E → F) (s : Set E)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    μ (f '' s) = 0 := by
  have hreg : ∀ x ∈ p ⁻¹' s, DifferentiableAt ℝ (f ∘ p) x := by
    intro x hx
    exact (hf (p x) hx).comp x p.differentiableAt
  have hcrit : ∀ x ∈ p ⁻¹' s, ¬ Function.Surjective (fderiv ℝ (f ∘ p) x) := by
    intro x hx hs
    have hd := ((hf (p x) hx).hasFDerivAt.comp x p.hasFDerivAt).fderiv
    rw [hd] at hs
    have hs' : Function.Surjective (fderiv ℝ f (p x)) := by
      intro y
      obtain ⟨z, hz⟩ := hs y
      exact ⟨p z, hz⟩
    have hr := LinearMap.finrank_range_le (fderiv ℝ f (p x)).toLinearMap
    rw [LinearMap.range_eq_top.mpr hs'] at hr
    simp at hr
    omega
  have hn := sameSpace_ambient_criticalImage_zero μ (f ∘ p) (p ⁻¹' s) hreg
  apply measure_mono_null _ hn
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨z, hz⟩ := hp x
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · change p z ∈ s
    simpa only [hz] using hx
  · exact hcrit z (by simpa only [Set.mem_preimage, hz] using hx)
  · change f (p z) = f x
    rw [hz]

#print axioms image_zero_of_lower_dimension_surjective_lift
