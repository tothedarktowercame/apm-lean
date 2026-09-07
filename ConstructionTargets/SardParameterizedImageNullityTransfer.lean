import ConstructionTargets.SardCriticalSetUnderParameterization

open Set MeasureTheory

namespace SardParameterizedImageNullityTransferProbe

/-- Images commute exactly with parameterized source images. -/
theorem image_image_eq_image_comp
    {E F G : Type*} (f : E → F) (g : G → E) (s : Set G) :
    f '' (g '' s) = (f ∘ g) '' s := by
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g z, ⟨z, hz, rfl⟩, rfl⟩

/-- Nullity of a parameterized composite image transfers to every source set
contained in the image of the parameter domain. -/
theorem image_null_of_subset_parameterized_image
    {E F G : Type*} [MeasurableSpace F] (μ : Measure F)
    (f : E → F) (g : G → E) (s : Set G) (t : Set E)
    (ht : t ⊆ g '' s) (hnull : μ ((f ∘ g) '' s) = 0) :
    μ (f '' t) = 0 := by
  apply measure_mono_null _ hnull
  rintro y ⟨x, hxt, rfl⟩
  obtain ⟨z, hzs, rfl⟩ := ht hxt
  exact ⟨z, hzs, rfl⟩

#print axioms image_image_eq_image_comp
#print axioms image_null_of_subset_parameterized_image
end SardParameterizedImageNullityTransferProbe
