import ConstructionTargets.KleinPlaneActionSquareOrbitClassification
import ConstructionTargets.StatementSurfaceModels

namespace KleinSurfaceRelNormalForm

open Set
open ConstructionTargets.Surfaces

theorem surfaceRel_false_two_iff (x y : Disk) :
    SurfaceRel false 2 x y ↔
      (∃ t : Set.Icc (0 : ℝ) 1,
        x = edgePoint 4 0 t ∧ y = edgePoint 4 1 t) ∨
      (∃ t : Set.Icc (0 : ℝ) 1,
        x = edgePoint 4 2 t ∧ y = edgePoint 4 3 t) := by
  constructor
  · rintro ⟨j, hj, t, hxt, hyt⟩
    interval_cases j
    · exact Or.inl ⟨t, by simpa using hxt, by simpa using hyt⟩
    · exact Or.inr ⟨t, by simpa using hxt, by simpa using hyt⟩
  · rintro (⟨t, hxt, hyt⟩ | ⟨t, hxt, hyt⟩)
    · exact ⟨0, by omega, t, by simpa using hxt, by simpa using hyt⟩
    · exact ⟨1, by omega, t, by simpa using hxt, by simpa using hyt⟩

#print axioms surfaceRel_false_two_iff

end KleinSurfaceRelNormalForm
