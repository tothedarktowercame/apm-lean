import ConstructionTargets.PolygonOuterRadialDeformation

open Set Topology
open unitInterval
noncomputable section

namespace ConstructionTargets.PolygonOuterRadialRelation

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonOuterRadialDeformation
open ConstructionTargets.RadialQuotientOpenSets

variable (R : Disk → Disk → Prop)

def OuterRel (x y : Outer) : Prop := R x.1 y.1

theorem outerRel_of_rel {x y : Outer} (h : R x.1 y.1) : OuterRel R x y := h

theorem radialHomotopy_rel
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (t : I) {x y : Outer} (hxy : OuterRel R x y) :
    OuterRel R (radialHomotopy (t, x)) (radialHomotopy (t, y)) := by
  rcases hboundary hxy with ⟨hx, hy⟩
  rw [radialHomotopy_fixed_of_radius_one t x hx,
    radialHomotopy_fixed_of_radius_one t y hy]
  exact hxy

theorem radialHomotopy_eqvGen
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (t : I) {x y : Outer} (hxy : Relation.EqvGen (OuterRel R) x y) :
    Relation.EqvGen (OuterRel R) (radialHomotopy (t, x))
      (radialHomotopy (t, y)) := by
  induction hxy with
  | rel x y h =>
      exact Relation.EqvGen.rel _ _ (radialHomotopy_rel R hboundary t h)
  | refl => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def quotientTimeSlice
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (t : I) :
    Quotient (Relation.EqvGen.setoid (OuterRel R)) →
      Quotient (Relation.EqvGen.setoid (OuterRel R)) :=
  Quotient.lift (fun x => Quotient.mk _ (radialHomotopy (t, x)))
    (fun _ _ h => Quotient.sound (radialHomotopy_eqvGen R hboundary t h))

theorem quotientTimeSlice_mk
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (t : I) (x : Outer) :
    quotientTimeSlice R hboundary t (Quotient.mk _ x) =
      Quotient.mk _ (radialHomotopy (t, x)) := rfl

theorem quotientTimeSlice_zero
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (z : Quotient (Relation.EqvGen.setoid (OuterRel R))) :
    quotientTimeSlice R hboundary 0 z = z := by
  induction z using Quotient.inductionOn with
  | _ x => simp [quotientTimeSlice, radialHomotopy_zero]

theorem surfaceRel_boundary (orientable : Bool) (genus : ℕ)
    {x y : Disk} (h : SurfaceRel orientable genus x y) :
    radius x = 1 ∧ radius y = 1 := by
  simp only [SurfaceRel] at h
  split at h
  · rcases h with ⟨j, hj, t, h | h⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨by simpa [radius] using norm_edgePoint (4 * genus) (4 * j) t,
        by simpa [radius] using
          norm_edgePoint (4 * genus) (4 * j + 2)
            ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨by simpa [radius] using norm_edgePoint (4 * genus) (4 * j + 1) t,
        by simpa [radius] using
          norm_edgePoint (4 * genus) (4 * j + 3)
            ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩⟩
  · rcases h with ⟨j, hj, t, rfl, rfl⟩
    exact ⟨by simpa [radius] using norm_edgePoint (2 * genus) (2 * j) t,
      by simpa [radius] using norm_edgePoint (2 * genus) (2 * j + 1) t⟩

end ConstructionTargets.PolygonOuterRadialRelation
