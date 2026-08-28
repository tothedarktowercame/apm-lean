import ConstructionTargets.SphereEquatorGluingOpenCover

/-!
# Coordinate presentation of the two-sphere equator gluing

This file isolates the representation change needed by the frozen `t96A03`
statement.  The frozen problem itself is not an importable Lake module, so the
final two definitions are deliberately phrased for a definition-for-definition
consumer in that file.
-/

open Set Topology

noncomputable section

namespace ConstructionTargets.T96A03FrozenQuotientRepresentation

open ConstructionTargets.SphereEquatorGluingOpenCover
open T02A06

/-- The nested-subtype presentation of the equator used by frozen `t96A03`. -/
abbrev CoordinateEquator :=
  {x : AmbientSphere 2 // (x.1 : EuclideanSpace ℝ (Fin 3)) 2 = 0}

/-- Remove the nested sphere subtype.  At dimension two, `Fin.last 2` is the
literal coordinate `2`. -/
def coordinateEquatorHomeomorph : CoordinateEquator ≃ₜ sphereEquator 2 where
  toFun x := ⟨x.1.1, x.1.2, by simpa using x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, by simpa using x.2.2⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
  continuous_toFun := continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- Conjugate a homeomorphism written in frozen coordinates to the reusable
equator representation. -/
def conjugateEquatorHomeomorph (h : CoordinateEquator ≃ₜ CoordinateEquator) :
    sphereEquator 2 ≃ₜ sphereEquator 2 :=
  coordinateEquatorHomeomorph.symm.trans
    (h.trans coordinateEquatorHomeomorph)

@[simp] theorem conjugateEquatorHomeomorph_apply
    (h : CoordinateEquator ≃ₜ CoordinateEquator) (x : CoordinateEquator) :
    conjugateEquatorHomeomorph h (coordinateEquatorHomeomorph x) =
      coordinateEquatorHomeomorph (h x) := by
  simp [conjugateEquatorHomeomorph]

/-- The generator relation in the nested coordinate presentation. -/
inductive CoordinateGlueRel (h : CoordinateEquator ≃ₜ CoordinateEquator) :
    Sum (AmbientSphere 2) (AmbientSphere 2) →
      Sum (AmbientSphere 2) (AmbientSphere 2) → Prop
  | glue (x : CoordinateEquator) :
      CoordinateGlueRel h (Sum.inl x.1) (Sum.inr (h x).1)

/-- The frozen generator relation and the reusable generator relation agree
after changing only the equator witness representation. -/
theorem coordinateGlueRel_iff_equatorGlueRel
    (h : CoordinateEquator ≃ₜ CoordinateEquator) (x y) :
    CoordinateGlueRel h x y ↔
      EquatorGlueRel 2 (conjugateEquatorHomeomorph h) x y := by
  constructor
  · rintro ⟨z⟩
    simpa [equatorInclusion, conjugateEquatorHomeomorph] using
      (EquatorGlueRel.glue (h := conjugateEquatorHomeomorph h)
        (coordinateEquatorHomeomorph z))
  · rintro ⟨z⟩
    simpa [equatorInclusion, conjugateEquatorHomeomorph] using
      (CoordinateGlueRel.glue (h := h) (coordinateEquatorHomeomorph.symm z))

/-- Consequently the generated equivalence relations are identical. -/
theorem coordinateEqvGen_iff_equatorEqvGen
    (h : CoordinateEquator ≃ₜ CoordinateEquator) (x y) :
    Relation.EqvGen (CoordinateGlueRel h) x y ↔
      Relation.EqvGen (EquatorGlueRel 2 (conjugateEquatorHomeomorph h)) x y := by
  constructor
  · intro hxy
    induction hxy with
    | rel a b hab => exact Relation.EqvGen.rel _ _ ((coordinateGlueRel_iff_equatorGlueRel h a b).mp hab)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    induction hxy with
    | rel a b hab => exact Relation.EqvGen.rel _ _ ((coordinateGlueRel_iff_equatorGlueRel h a b).mpr hab)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The quotient written with the nested coordinate equator. -/
abbrev CoordinateGluing (h : CoordinateEquator ≃ₜ CoordinateEquator) :=
  Quotient (Relation.EqvGen.setoid (CoordinateGlueRel h))

noncomputable instance (h : CoordinateEquator ≃ₜ CoordinateEquator) :
    TopologicalSpace (CoordinateGluing h) :=
  TopologicalSpace.coinduced
    (fun x : Sum (AmbientSphere 2) (AmbientSphere 2) ↦ Quotient.mk _ x)
    inferInstance

/-- The two quotient presentations are homeomorphic.  On representatives the
map is literally the identity; only the proof that the generated relations
agree changes. -/
def coordinateGluingHomeomorph (h : CoordinateEquator ≃ₜ CoordinateEquator) :
    CoordinateGluing h ≃ₜ EquatorGluing 2 (conjugateEquatorHomeomorph h) where
  toFun := Quotient.lift (fun x ↦ Quotient.mk _ x) fun _ _ hxy ↦
    Quotient.sound ((coordinateEqvGen_iff_equatorEqvGen h _ _).mp hxy)
  invFun := Quotient.lift (fun x ↦ Quotient.mk _ x) fun _ _ hxy ↦
    Quotient.sound ((coordinateEqvGen_iff_equatorEqvGen h _ _).mpr hxy)
  left_inv := by rintro ⟨x⟩; rfl
  right_inv := by rintro ⟨x⟩; rfl
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng

@[simp] theorem coordinateGluingHomeomorph_mk
    (h : CoordinateEquator ≃ₜ CoordinateEquator)
    (x : Sum (AmbientSphere 2) (AmbientSphere 2)) :
    coordinateGluingHomeomorph h (Quotient.mk _ x) = Quotient.mk _ x := rfl

#print axioms coordinateEquatorHomeomorph
#print axioms conjugateEquatorHomeomorph
#print axioms coordinateEqvGen_iff_equatorEqvGen
#print axioms coordinateGluingHomeomorph

end ConstructionTargets.T96A03FrozenQuotientRepresentation
