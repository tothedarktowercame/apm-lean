import ConstructionTargets.SardScalarizedJetImplicitFunctionData
import ConstructionTargets.SardImplicitFunctionLevelSetCoordinates

namespace SardImplicitFunctionLevelSetImageProbe

variable {E F G : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

/-- An open partial homeomorphism maps its source-localized constant-first-
coordinate locus exactly onto the corresponding slice of its target. -/
theorem OpenPartialHomeomorph.image_inter_source_fst_eq
    (e : OpenPartialHomeomorph E (F × G)) (c : F) :
    e '' (e.source ∩ {y | (e y).1 = c}) = e.target ∩ {z | z.1 = c} := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hfirst⟩, rfl⟩
    exact ⟨e.map_source hy, hfirst⟩
  · rintro ⟨hz, hfirst⟩
    refine ⟨e.symm z, ⟨e.symm.map_source hz, ?_⟩, e.right_inv hz⟩
    change (e (e.symm z)).1 = c
    rw [e.right_inv hz]
    exact hfirst

end SardImplicitFunctionLevelSetImageProbe

namespace SardImplicitFunctionLevelSetImageProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The exact implicit-function chart sends a localized left level set onto
the constant-first-coordinate slice of its chart target. -/
theorem ImplicitFunctionData.image_inter_source_leftFun_level_eq
    (φ : ImplicitFunctionData ℝ E F G) (c : F) :
    φ.toOpenPartialHomeomorph ''
        (φ.toOpenPartialHomeomorph.source ∩ {y | φ.leftFun y = c}) =
      φ.toOpenPartialHomeomorph.target ∩ {z | z.1 = c} := by
  rw [SardImplicitFunctionLevelSetCoordinatesProbe.ImplicitFunctionData.inter_source_leftFun_level_eq]
  exact OpenPartialHomeomorph.image_inter_source_fst_eq φ.toOpenPartialHomeomorph c

#print axioms OpenPartialHomeomorph.image_inter_source_fst_eq
#print axioms ImplicitFunctionData.image_inter_source_leftFun_level_eq
end SardImplicitFunctionLevelSetImageProbe
