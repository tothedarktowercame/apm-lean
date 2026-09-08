import ConstructionTargets.SardImplicitFunctionKernelParameterLocalRegularity
import ConstructionTargets.SardImplicitFunctionLevelSetKernelParameterization

open Set

namespace SardImplicitFunctionRestrictedKernelParameterizationProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Restricting the right-coordinate parameter set by an open neighborhood
corresponds exactly to intersecting the source level hypersurface with the
associated open chart neighborhood. -/
theorem ImplicitFunctionData.image_restricted_kernelParameter_eq
    (φ : ImplicitFunctionData ℝ E F G) (V : Set G) :
    (fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)) ''
        ({z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target} ∩ V) =
      (φ.toOpenPartialHomeomorph.source ∩
          φ.toOpenPartialHomeomorph ⁻¹' (Set.univ ×ˢ V)) ∩
        {y | φ.leftFun y = φ.leftFun φ.pt} := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzt, hzV⟩, rfl⟩
    have hys := φ.toOpenPartialHomeomorph.symm.map_source hzt
    have hry := φ.toOpenPartialHomeomorph.right_inv hzt
    refine ⟨⟨hys, ?_⟩, ?_⟩
    · change φ.toOpenPartialHomeomorph
          (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)) ∈ Set.univ ×ˢ V
      rw [hry]
      exact ⟨Set.mem_univ _, hzV⟩
    · change φ.leftFun (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)) =
        φ.leftFun φ.pt
      have := congrArg Prod.fst hry
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply] using this
  · rintro ⟨⟨hys, hyV⟩, hlevel⟩
    refine ⟨φ.rightFun y, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [← hlevel]
        exact φ.toOpenPartialHomeomorph.map_source hys
      · change φ.toOpenPartialHomeomorph y ∈ Set.univ ×ˢ V at hyV
        exact hyV.2
    · rw [← hlevel]
      exact φ.toOpenPartialHomeomorph.left_inv hys

/-- An open right-coordinate neighborhood of the base point induces an open
source neighborhood of the implicit-function base point. -/
theorem ImplicitFunctionData.isOpen_source_restrict_right
    (φ : ImplicitFunctionData ℝ E F G) (V : Set G) (hV : IsOpen V) :
    IsOpen (φ.toOpenPartialHomeomorph.source ∩
      φ.toOpenPartialHomeomorph ⁻¹' (Set.univ ×ˢ V)) :=
  φ.toOpenPartialHomeomorph.isOpen_inter_preimage (isOpen_univ.prod hV)

theorem ImplicitFunctionData.pt_mem_source_restrict_right
    (φ : ImplicitFunctionData ℝ E F G) (V : Set G)
    (hV : φ.rightFun φ.pt ∈ V) :
    φ.pt ∈ φ.toOpenPartialHomeomorph.source ∩
      φ.toOpenPartialHomeomorph ⁻¹' (Set.univ ×ˢ V) := by
  refine ⟨φ.pt_mem_toOpenPartialHomeomorph_source, ?_⟩
  exact ⟨Set.mem_univ _, hV⟩

#print axioms ImplicitFunctionData.image_restricted_kernelParameter_eq
#print axioms ImplicitFunctionData.isOpen_source_restrict_right
#print axioms ImplicitFunctionData.pt_mem_source_restrict_right
end SardImplicitFunctionRestrictedKernelParameterizationProbe
