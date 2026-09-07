import ConstructionTargets.SardImplicitFunctionKernelSliceParameterization

namespace SardImplicitFunctionLevelSetKernelParameterizationProbe

variable {E F G : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

/-- Pulling the constant-first-coordinate target slice back through the chart
inverse parameterizes the corresponding source locus by the second coordinate. -/
theorem OpenPartialHomeomorph.image_symm_mk_left_eq_inter_source_fst
    (e : OpenPartialHomeomorph E (F × G)) (c : F) :
    (fun z : G => e.symm (c, z)) '' {z | (c, z) ∈ e.target} =
      e.source ∩ {y | (e y).1 = c} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨e.symm.map_source hz, ?_⟩
    change (e (e.symm (c, z))).1 = c
    rw [e.right_inv hz]
  · rintro ⟨hy, hfirst⟩
    change (e y).1 = c at hfirst
    refine ⟨(e y).2, ?_, ?_⟩
    · change (c, (e y).2) ∈ e.target
      rw [show (c, (e y).2) = e y by ext <;> simp [hfirst]]
      exact e.map_source hy
    · change e.symm (c, (e y).2) = y
      rw [show (c, (e y).2) = e y by ext <;> simp [hfirst]]
      exact e.left_inv hy

end SardImplicitFunctionLevelSetKernelParameterizationProbe

namespace SardImplicitFunctionLevelSetKernelParameterizationProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The inverse exact implicit-function chart parameterizes its localized left
level set by a subset of the right-coordinate space alone. -/
theorem ImplicitFunctionData.image_kernelParam_eq_inter_source_leftFun_level
    (φ : ImplicitFunctionData ℝ E F G) (c : F) :
    (fun z : G => φ.toOpenPartialHomeomorph.symm (c, z)) ''
        {z | (c, z) ∈ φ.toOpenPartialHomeomorph.target} =
      φ.toOpenPartialHomeomorph.source ∩ {y | φ.leftFun y = c} := by
  rw [SardImplicitFunctionLevelSetCoordinatesProbe.ImplicitFunctionData.inter_source_leftFun_level_eq]
  exact OpenPartialHomeomorph.image_symm_mk_left_eq_inter_source_fst
    φ.toOpenPartialHomeomorph c

#print axioms OpenPartialHomeomorph.image_symm_mk_left_eq_inter_source_fst
#print axioms ImplicitFunctionData.image_kernelParam_eq_inter_source_leftFun_level
end SardImplicitFunctionLevelSetKernelParameterizationProbe
