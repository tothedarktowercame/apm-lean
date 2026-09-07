import ConstructionTargets.SardImplicitFunctionLevelSetImage

namespace SardImplicitFunctionKernelSliceParameterizationProbe

variable {F G : Type*}

/-- A constant-first-coordinate slice is exactly parameterized by its second
coordinate, with domain cut out by membership in the ambient set. -/
theorem image_mk_left_preimage_eq_inter_fst
    (t : Set (F × G)) (c : F) :
    (fun z : G => (c, z)) '' {z | (c, z) ∈ t} = t ∩ {p | p.1 = c} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, rfl⟩
  · rintro ⟨hp, hfirst⟩
    rcases p with ⟨a, b⟩
    change a = c at hfirst
    subst a
    exact ⟨b, hp, rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The target slice of an exact implicit-function chart is the image of a
set in the right-coordinate space alone. -/
theorem ImplicitFunctionData.target_inter_fst_eq_image_kernelSlice
    (φ : ImplicitFunctionData ℝ E F G) (c : F) :
    φ.toOpenPartialHomeomorph.target ∩ {p | p.1 = c} =
      (fun z : G => (c, z)) '' {z | (c, z) ∈ φ.toOpenPartialHomeomorph.target} := by
  symm
  exact image_mk_left_preimage_eq_inter_fst φ.toOpenPartialHomeomorph.target c

#print axioms image_mk_left_preimage_eq_inter_fst
#print axioms ImplicitFunctionData.target_inter_fst_eq_image_kernelSlice
end SardImplicitFunctionKernelSliceParameterizationProbe
