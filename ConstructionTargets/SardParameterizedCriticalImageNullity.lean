import ConstructionTargets.SardParameterizedImageNullityTransfer

open Set MeasureTheory

namespace SardParameterizedCriticalImageNullityProbe

/-- Nullity of the full critical image of a parameterized composite transfers
to any parameterized localized set consisting of critical points of the
original map. -/
theorem localizedCriticalImage_null_of_parameterized
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure F) (f : E → F) (g : G → E) (s : Set G) (t : Set E)
    (hparam : t ⊆ g '' s)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f (g z))
    (hg : ∀ z ∈ s, DifferentiableAt ℝ g z)
    (htcrit : ∀ x ∈ t, ¬ Function.Surjective (fderiv ℝ f x))
    (hnull : μ ((f ∘ g) ''
      {z | ¬ Function.Surjective (fderiv ℝ (f ∘ g) z)}) = 0) :
    μ (f '' t) = 0 := by
  apply SardParameterizedImageNullityTransferProbe.image_null_of_subset_parameterized_image
    μ f g {z | ¬ Function.Surjective (fderiv ℝ (f ∘ g) z)} t _ hnull
  intro x hx
  obtain ⟨z, hzs, rfl⟩ := hparam hx
  refine ⟨z, ?_, rfl⟩
  exact SardCriticalSetUnderParameterizationProbe.not_surjective_fderiv_comp
    (hf z hzs) (hg z hzs) (htcrit (g z) hx)

#print axioms localizedCriticalImage_null_of_parameterized
end SardParameterizedCriticalImageNullityProbe
