import ConstructionTargets.SolidTorusGluingOpenCover

/-!
# Coordinate presentation of the solid-torus boundary gluing

This isolates the representation change required by frozen `t01J03`.  The
frozen problem is not an importable Lake module, so the final consumer step is
phrased using definition-for-definition coordinate types.
-/

open Set Topology

noncomputable section

namespace ConstructionTargets.T01J03FrozenQuotientRepresentation

open ConstructionTargets.SolidTorusGluingOpenCover

abbrev CoordinatePlane := EuclideanSpace ℝ (Fin 2)
abbrev CoordinateDisk := Metric.closedBall (0 : CoordinatePlane) 1
abbrev CoordinateBoundaryCircle := Metric.sphere (0 : CoordinatePlane) 1
abbrev CoordinateSolidTorus := Circle × CoordinateDisk
abbrev CoordinateBoundaryTorus := Circle × CoordinateBoundaryCircle

def coordinateSolidTorusHomeomorph : CoordinateSolidTorus ≃ₜ SolidTorus :=
  Homeomorph.refl _

def coordinateBoundaryTorusHomeomorph :
    CoordinateBoundaryTorus ≃ₜ BoundaryTorus :=
  Homeomorph.refl _

def coordinateBoundaryInclusion :
    CoordinateBoundaryTorus → CoordinateSolidTorus :=
  fun z ↦ (z.1, ⟨z.2.1, le_of_eq z.2.2⟩)

theorem coordinateBoundaryInclusion_compatibility
    (z : CoordinateBoundaryTorus) :
    coordinateSolidTorusHomeomorph (coordinateBoundaryInclusion z) =
      boundaryInclusion (coordinateBoundaryTorusHomeomorph z) := rfl

theorem continuous_coordinateBoundaryInclusion :
    Continuous coordinateBoundaryInclusion :=
  continuous_boundaryInclusion

def conjugateBoundaryHomeomorph
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus) :
    BoundaryTorus ≃ₜ BoundaryTorus :=
  coordinateBoundaryTorusHomeomorph.symm.trans
    (h.trans coordinateBoundaryTorusHomeomorph)

@[simp] theorem conjugateBoundaryHomeomorph_apply
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus)
    (z : CoordinateBoundaryTorus) :
    conjugateBoundaryHomeomorph h (coordinateBoundaryTorusHomeomorph z) =
      coordinateBoundaryTorusHomeomorph (h z) := by
  simp [conjugateBoundaryHomeomorph]

def coordinatePieceHomeomorph :
    Sum CoordinateSolidTorus CoordinateSolidTorus ≃ₜ
      Sum SolidTorus SolidTorus :=
  Homeomorph.refl _

inductive CoordinateGlueRel
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus) :
    Sum CoordinateSolidTorus CoordinateSolidTorus →
      Sum CoordinateSolidTorus CoordinateSolidTorus → Prop
  | glue (z : CoordinateBoundaryTorus) :
      CoordinateGlueRel h
        (Sum.inl (coordinateBoundaryInclusion z))
        (Sum.inr (coordinateBoundaryInclusion (h z)))

theorem coordinateGlueRel_iff_boundaryGlueRel
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus) (x y) :
    CoordinateGlueRel h x y ↔
      BoundaryGlueRel (conjugateBoundaryHomeomorph h)
        (coordinatePieceHomeomorph x) (coordinatePieceHomeomorph y) := by
  constructor
  · rintro ⟨z⟩
    simpa [coordinatePieceHomeomorph, coordinateBoundaryInclusion,
      boundaryInclusion, conjugateBoundaryHomeomorph] using
      (BoundaryGlueRel.glue (h := conjugateBoundaryHomeomorph h)
        (coordinateBoundaryTorusHomeomorph z))
  · rintro ⟨z⟩
    simpa [coordinatePieceHomeomorph, coordinateBoundaryInclusion,
      boundaryInclusion, conjugateBoundaryHomeomorph] using
      (CoordinateGlueRel.glue (h := h)
        (coordinateBoundaryTorusHomeomorph.symm z))

theorem coordinateEqvGen_iff_boundaryEqvGen
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus) (x y) :
    Relation.EqvGen (CoordinateGlueRel h) x y ↔
      Relation.EqvGen (BoundaryGlueRel (conjugateBoundaryHomeomorph h)) x y := by
  constructor
  · intro hxy
    induction hxy with
    | rel a b hab =>
        exact Relation.EqvGen.rel _ _
          ((coordinateGlueRel_iff_boundaryGlueRel h a b).mp hab)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    induction hxy with
    | rel a b hab =>
        exact Relation.EqvGen.rel _ _
          ((coordinateGlueRel_iff_boundaryGlueRel h a b).mpr hab)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

abbrev CoordinateGluing
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus) :=
  Quotient (Relation.EqvGen.setoid (CoordinateGlueRel h))

noncomputable instance
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus) :
    TopologicalSpace (CoordinateGluing h) :=
  TopologicalSpace.coinduced
    (fun x : Sum CoordinateSolidTorus CoordinateSolidTorus ↦ Quotient.mk _ x)
    inferInstance

def coordinateGluingHomeomorph
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus) :
    CoordinateGluing h ≃ₜ Gluing (conjugateBoundaryHomeomorph h) where
  toFun := Quotient.lift
    (fun x ↦ Quotient.mk _ (coordinatePieceHomeomorph x)) fun _ _ hxy ↦
      Quotient.sound ((coordinateEqvGen_iff_boundaryEqvGen h _ _).mp hxy)
  invFun := Quotient.lift
    (fun x ↦ Quotient.mk _ (coordinatePieceHomeomorph.symm x)) fun _ _ hxy ↦
      Quotient.sound ((coordinateEqvGen_iff_boundaryEqvGen h _ _).mpr <| by
        simpa using hxy)
  left_inv := by rintro ⟨x⟩; exact congrArg (Quotient.mk _) (coordinatePieceHomeomorph.left_inv x)
  right_inv := by rintro ⟨x⟩; exact congrArg (Quotient.mk _) (coordinatePieceHomeomorph.right_inv x)
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng.comp coordinatePieceHomeomorph.continuous
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng.comp coordinatePieceHomeomorph.symm.continuous

@[simp] theorem coordinateGluingHomeomorph_mk
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus)
    (x : Sum CoordinateSolidTorus CoordinateSolidTorus) :
    coordinateGluingHomeomorph h (Quotient.mk _ x) =
      Quotient.mk _ (coordinatePieceHomeomorph x) := rfl

@[simp] theorem coordinateGluingHomeomorph_symm_mk
    (h : CoordinateBoundaryTorus ≃ₜ CoordinateBoundaryTorus)
    (x : Sum SolidTorus SolidTorus) :
    (coordinateGluingHomeomorph h).symm (Quotient.mk _ x) =
      Quotient.mk _ (coordinatePieceHomeomorph.symm x) := rfl

#print axioms coordinateSolidTorusHomeomorph
#print axioms coordinateBoundaryInclusion_compatibility
#print axioms coordinateGlueRel_iff_boundaryGlueRel
#print axioms coordinateEqvGen_iff_boundaryEqvGen
#print axioms coordinateGluingHomeomorph

end ConstructionTargets.T01J03FrozenQuotientRepresentation
