import ConstructionTargets.SardImplicitFunctionRestrictedKernelParameterization

open Set

namespace SardImplicitFunctionRestrictedSliceImageContainmentProbe

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A source subset lying in the fixed left-coordinate level set is locally
parameterized by the restricted inverse-chart kernel slice, also after applying
an arbitrary target map. -/
theorem ImplicitFunctionData.image_inter_sourceRestrict_subset_image_comp_kernelParameter
    (φ : ImplicitFunctionData ℝ E F G) (f : E → H) (t : Set E) (V : Set G)
    (ht : t ⊆ {y | φ.leftFun y = φ.leftFun φ.pt}) :
    f '' (t ∩ (φ.toOpenPartialHomeomorph.source ∩
      φ.toOpenPartialHomeomorph ⁻¹' (Set.univ ×ˢ V))) ⊆
      (f ∘ fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)) ''
        ({z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target} ∩ V) := by
  intro w hw
  obtain ⟨y, ⟨hyt, hyU⟩, rfl⟩ := hw
  have hy : y ∈
      (φ.toOpenPartialHomeomorph.source ∩
        φ.toOpenPartialHomeomorph ⁻¹' (Set.univ ×ˢ V)) ∩
          {y | φ.leftFun y = φ.leftFun φ.pt} := ⟨hyU, ht hyt⟩
  rw [← SardImplicitFunctionRestrictedKernelParameterizationProbe.ImplicitFunctionData.image_restricted_kernelParameter_eq φ V] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨z, hz, rfl⟩

#print axioms ImplicitFunctionData.image_inter_sourceRestrict_subset_image_comp_kernelParameter
end SardImplicitFunctionRestrictedSliceImageContainmentProbe
