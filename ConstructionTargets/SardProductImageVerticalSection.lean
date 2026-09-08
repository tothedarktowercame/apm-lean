import Mathlib

open Set

namespace SardProductImageVerticalSectionProbe

/-- A vertical section of a product-valued image is exactly the image of the
corresponding fixed-first-coordinate source fiber under the second coordinate. -/
theorem prodMk_preimage_image_eq_snd_image_fstFiber
    {E R S : Type*} (q : E → R × S) (K : Set E) (r : R) :
    Prod.mk r ⁻¹' (q '' K) =
      (fun x => (q x).2) '' (K ∩ {x | (q x).1 = r}) := by
  ext s
  constructor
  · rintro ⟨x, hxK, hxq⟩
    refine ⟨x, ⟨hxK, ?_⟩, ?_⟩
    · exact congrArg Prod.fst hxq
    · exact congrArg Prod.snd hxq
  · rintro ⟨x, ⟨hxK, hxr⟩, rfl⟩
    refine ⟨x, hxK, ?_⟩
    exact Prod.ext hxr rfl

#print axioms prodMk_preimage_image_eq_snd_image_fstFiber
end SardProductImageVerticalSectionProbe
