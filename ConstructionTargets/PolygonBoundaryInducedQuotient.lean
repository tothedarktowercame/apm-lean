import ConstructionTargets.PolygonBoundaryCircleSource

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonBoundaryInducedQuotient

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonBoundaryCircleSource

universe u v

theorem eqvGen_map {A : Type u} {B : Type v}
    (R : A → A → Prop) (S : B → B → Prop) (f : A → B)
    (hf : ∀ ⦃a b⦄, R a b → S (f a) (f b))
    {a b : A} (h : Relation.EqvGen R a b) :
    Relation.EqvGen S (f a) (f b) := by
  induction h with
  | rel a b h => exact .rel _ _ (hf h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

variable (R : Disk → Disk → Prop)

def BoundaryRel (x y : Boundary) : Prop := R x.1 y.1

def CircleRel (z w : Circle) : Prop :=
  BoundaryRel R (circleToBoundary z) (circleToBoundary w)

abbrev CircleQuotient := Quotient (Relation.EqvGen.setoid (CircleRel R))
abbrev BoundaryQuotient := Quotient (Relation.EqvGen.setoid (BoundaryRel R))

noncomputable instance : TopologicalSpace (CircleQuotient R) :=
  TopologicalSpace.coinduced (fun z : Circle => Quotient.mk _ z) inferInstance

noncomputable instance : TopologicalSpace (BoundaryQuotient R) :=
  TopologicalSpace.coinduced (fun x : Boundary => Quotient.mk _ x) inferInstance

def circleBoundaryQuotientHomeomorph : CircleQuotient R ≃ₜ BoundaryQuotient R where
  toFun := Quotient.lift
    (fun z : Circle => Quotient.mk _ (circleToBoundary z))
    (fun a b hab => Quotient.sound
      (eqvGen_map (CircleRel R) (BoundaryRel R) circleToBoundary
        (fun {_ _} h => h) hab))
  invFun := Quotient.lift
    (fun x : Boundary => Quotient.mk _ (boundaryToCircle x))
    (fun _ _ h => Quotient.sound (eqvGen_map (BoundaryRel R) (CircleRel R)
      boundaryToCircle (by
      intro x y hxy
      simpa [CircleRel, BoundaryRel] using hxy) h))
  left_inv := by
    rintro ⟨z⟩
    change Quotient.mk _ (boundaryToCircle (circleToBoundary z)) = Quotient.mk _ z
    rw [boundaryToCircle_circleToBoundary]
  right_inv := by
    rintro ⟨x⟩
    change Quotient.mk _ (circleToBoundary (boundaryToCircle x)) = Quotient.mk _ x
    rw [circleToBoundary_boundaryToCircle]
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng.comp boundaryCircleHomeomorph.continuous
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng.comp boundaryCircleHomeomorph.symm.continuous

@[simp] theorem circleBoundaryQuotientHomeomorph_mk (z : Circle) :
    circleBoundaryQuotientHomeomorph R (Quotient.mk _ z) =
      Quotient.mk _ (circleToBoundary z) := rfl

@[simp] theorem circleBoundaryQuotientHomeomorph_symm_mk (x : Boundary) :
    (circleBoundaryQuotientHomeomorph R).symm (Quotient.mk _ x) =
      Quotient.mk _ (boundaryToCircle x) := rfl

end ConstructionTargets.PolygonBoundaryInducedQuotient
