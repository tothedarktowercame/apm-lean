import ConstructionTargets.PolygonOuterOpenDeformation

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonAnnularOverlapHomeomorph

open ConstructionTargets.Surfaces
open ConstructionTargets.RadialQuotientOpenSets
open ConstructionTargets.PolygonRadialOpenCover

variable (R : Surfaces.Disk → Surfaces.Disk → Prop)

abbrev Annulus := {x : Surfaces.Disk // x ∈ overlapSource}

theorem eq_of_eqvGen_of_radius_lt_one
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    {x y : Surfaces.Disk} (hxy : Relation.EqvGen R x y)
    (hx : radius x < 1) : x = y := by
  induction hxy with
  | rel x y h =>
      have hx1 := (hboundary h).1
      linarith
  | refl => rfl
  | symm x y h ih =>
      have hr : radius x = radius y :=
        eqvGen_preserves_of_rel_preserves R radius hR h
      exact (ih (by linarith)).symm
  | trans x y z hxy hyz ih₁ ih₂ =>
      have hxy' : x = y := ih₁ hx
      exact hxy'.trans (ih₂ (hxy' ▸ hx))

theorem quotientMap_preimage_overlapOpen
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    quotientMap R ⁻¹' overlapOpen R = overlapSource := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have he : Relation.EqvGen R y x := Quotient.exact hxy
    have hr : radius y = radius x :=
      eqvGen_preserves_of_rel_preserves R radius hR he
    rcases hy with ⟨hyI, hyO⟩
    change radius y < 3 / 4 at hyI
    change 1 / 4 < radius y at hyO
    constructor
    · change radius x < 3 / 4
      linarith
    · change 1 / 4 < radius x
      linarith
  · intro hx
    exact ⟨x, hx, rfl⟩

def overlapMap : Annulus → overlapOpen R :=
  fun x => ⟨quotientMap R x.1, ⟨x.1, x.2, rfl⟩⟩

theorem overlapMap_isQuotientMap
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    IsQuotientMap (overlapMap R) := by
  let e : {x : Surfaces.Disk // quotientMap R x ∈ overlapOpen R} ≃ₜ Annulus :=
    Homeomorph.setCongr (quotientMap_preimage_overlapOpen R hR)
  have hq : IsQuotientMap
      ((overlapOpen R).restrictPreimage (quotientMap R)) := by
    apply isQuotientMap_quotient_mk'.restrictPreimage_isOpen
    exact isOpen_radial_image R radius continuous_radius hR _
      ((isOpen_Iio.inter isOpen_Ioi))
  have heq : overlapMap R =
      ((overlapOpen R).restrictPreimage (quotientMap R)) ∘ e.symm := by
    funext x
    apply Subtype.ext
    rfl
  rw [heq]
  exact hq.comp e.symm.isQuotientMap

theorem overlapMap_injective
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    Function.Injective (overlapMap R) := by
  intro x y hxy
  apply Subtype.ext
  have he : Relation.EqvGen R x.1 y.1 :=
    Quotient.exact (congrArg Subtype.val hxy)
  apply eq_of_eqvGen_of_radius_lt_one R hR hboundary he
  exact lt_trans x.2.1 (by norm_num)

def overlapHomeomorph
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    Annulus ≃ₜ overlapOpen R := by
  let hq := overlapMap_isQuotientMap R hR
  let hi := overlapMap_injective R hR hboundary
  let e : Annulus ≃ overlapOpen R :=
    Equiv.ofBijective (overlapMap R) ⟨hi, hq.surjective⟩
  exact {
    toEquiv := e
    continuous_toFun := hq.continuous
    continuous_invFun := by
      rw [hq.continuous_iff]
      convert continuous_id
      funext x
      exact e.symm_apply_apply x }

theorem overlapHomeomorph_apply
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (x : Annulus) :
    overlapHomeomorph R hR hboundary x = overlapMap R x := rfl

end ConstructionTargets.PolygonAnnularOverlapHomeomorph
