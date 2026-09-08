import ConstructionTargets.SardImplicitFunctionRestrictedKernelParameterization
import ConstructionTargets.SardParameterizedImageNullityTransfer
import ConstructionTargets.SardCriticalSetUnderParameterization

open Set MeasureTheory

namespace SardParameterizedLocalCriticalImageNullityProbe

/-- Nullity of the composite critical image restricted to the parameter set
transfers to a parameterized localized critical set of the original map. -/
theorem localizedCriticalImage_null_of_parameterized_on
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
      (s ∩ {z | ¬ Function.Surjective (fderiv ℝ (f ∘ g) z)})) = 0) :
    μ (f '' t) = 0 := by
  apply SardParameterizedImageNullityTransferProbe.image_null_of_subset_parameterized_image
    μ f g (s ∩ {z | ¬ Function.Surjective (fderiv ℝ (f ∘ g) z)}) t _ hnull
  intro x hx
  obtain ⟨z, hzs, rfl⟩ := hparam hx
  refine ⟨z, ⟨hzs, ?_⟩, rfl⟩
  exact SardCriticalSetUnderParameterizationProbe.not_surjective_fderiv_comp
    (hf z hzs) (hg z hzs) (htcrit (g z) hx)

#print axioms localizedCriticalImage_null_of_parameterized_on
end SardParameterizedLocalCriticalImageNullityProbe
