import ConstructionTargets.PolygonOuterOpenRestrictedQuotient

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonOuterRestrictedEqvGen

open ConstructionTargets.Surfaces
open ConstructionTargets.RadialQuotientOpenSets
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonOuterRadialDeformation
open ConstructionTargets.PolygonOuterRadialRelation
open ConstructionTargets.PolygonOuterOpenRestrictedQuotient

variable (R : Surfaces.Disk → Surfaces.Disk → Prop)

theorem eqvGen_outerRel_of_eqvGen
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    {x y : Outer} (hxy : Relation.EqvGen R x.1 y.1) :
    Relation.EqvGen (OuterRel R) x y := by
  have lift : ∀ {a b : Surfaces.Disk}, Relation.EqvGen R a b →
      ∀ (ha : a ∈ outerSource) (hb : b ∈ outerSource),
        Relation.EqvGen (OuterRel R) ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b hab
    induction hab with
    | rel a b hab =>
        intro ha hb
        exact Relation.EqvGen.rel _ _ hab
    | refl a =>
        intro ha hb
        exact Relation.EqvGen.refl _
    | symm a b hab ih =>
        intro ha hb
        exact (ih hb ha).symm
    | trans a b c hab hbc ih₁ ih₂ =>
        intro ha hc
        have hr : radius a = radius b :=
          eqvGen_preserves_of_rel_preserves R radius hR hab
        have hb : b ∈ outerSource := by
          change 1 / 4 < radius b
          change 1 / 4 < radius a at ha
          linarith
        exact Relation.EqvGen.trans _ _ _ (ih₁ ha hb) (ih₂ hb hc)
  exact lift hxy x.2 y.2

theorem eqvGen_of_eqvGen_outerRel {x y : Outer}
    (hxy : Relation.EqvGen (OuterRel R) x y) :
    Relation.EqvGen R x.1 y.1 := by
  induction hxy with
  | rel x y h => exact Relation.EqvGen.rel _ _ h
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem namedOuterQuotientMap_eq_iff {x y : Outer}
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    namedOuterQuotientMap R hR x = namedOuterQuotientMap R hR y ↔
      Relation.EqvGen (OuterRel R) x y := by
  rw [Subtype.ext_iff]
  change Quotient.mk _ x.1 = Quotient.mk _ y.1 ↔ _
  rw [Quotient.eq]
  exact ⟨eqvGen_outerRel_of_eqvGen R hR, eqvGen_of_eqvGen_outerRel R⟩

abbrev OuterQuotient := Quotient (Relation.EqvGen.setoid (OuterRel R))

def outerQuotientHomeomorph
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    OuterQuotient R ≃ₜ outerOpen R :=
  let f : C(Outer, outerOpen R) :=
    ⟨namedOuterQuotientMap R hR,
      (namedOuterQuotientMap_isQuotientMap R hR).continuous⟩
  let hf := namedOuterQuotientMap_isQuotientMap R hR
  let e : OuterQuotient R ≃ₜ Quotient (Setoid.ker f) := {
    toFun := Quotient.lift (fun x => Quotient.mk _ x) (fun _ _ h =>
      Quotient.sound ((namedOuterQuotientMap_eq_iff R hR).mpr h))
    invFun := Quotient.lift (fun x => Quotient.mk _ x) (fun _ _ h =>
      Quotient.sound ((namedOuterQuotientMap_eq_iff R hR).mp h))
    left_inv := by rintro ⟨x⟩; rfl
    right_inv := by rintro ⟨x⟩; rfl
    continuous_toFun := by apply Continuous.quotient_lift; exact continuous_quotient_mk'
    continuous_invFun := by apply Continuous.quotient_lift; exact continuous_quotient_mk' }
  e.trans hf.homeomorph

theorem outerQuotientHomeomorph_mk
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) (x : Outer) :
    outerQuotientHomeomorph R hR (Quotient.mk _ x) =
      namedOuterQuotientMap R hR x := by
  rfl

end ConstructionTargets.PolygonOuterRestrictedEqvGen
