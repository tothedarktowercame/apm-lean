import ConstructionTargets.PolygonOuterRadialQuotientDeformation

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonOuterOpenRestrictedQuotient

open ConstructionTargets.Surfaces
open ConstructionTargets.RadialQuotientOpenSets
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonOuterRadialDeformation

variable (R : Surfaces.Disk → Surfaces.Disk → Prop)

theorem quotientMap_preimage_outerOpen
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    quotientMap R ⁻¹' outerOpen R = outerSource := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have he : Relation.EqvGen R y x := Quotient.exact hxy
    have hr : radius y = radius x :=
      eqvGen_preserves_of_rel_preserves R radius hR he
    change 1 / 4 < radius x
    change 1 / 4 < radius y at hy
    linarith
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem quotientMap_isQuotientMap :
    IsQuotientMap (quotientMap R) := by
  exact isQuotientMap_quotient_mk'

def restrictedQuotientMap :
    {x : Surfaces.Disk // quotientMap R x ∈ outerOpen R} → outerOpen R :=
  (outerOpen R).restrictPreimage (quotientMap R)

theorem restrictedQuotientMap_isQuotientMap
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    IsQuotientMap (restrictedQuotientMap R) := by
  exact (quotientMap_isQuotientMap R).restrictPreimage_isOpen
    (outerOpen_isOpen R hR)

def outerPreimageHomeomorph
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    {x : Surfaces.Disk // quotientMap R x ∈ outerOpen R} ≃ₜ Outer :=
  Homeomorph.setCongr (quotientMap_preimage_outerOpen R hR)

def namedOuterQuotientMap
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    Outer → outerOpen R :=
  restrictedQuotientMap R ∘ (outerPreimageHomeomorph R hR).symm

theorem namedOuterQuotientMap_isQuotientMap
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    IsQuotientMap (namedOuterQuotientMap R hR) :=
  (restrictedQuotientMap_isQuotientMap R hR).comp
    (outerPreimageHomeomorph R hR).symm.isQuotientMap

theorem namedOuterQuotientMap_apply
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) (x : Outer) :
    (namedOuterQuotientMap R hR x).1 = quotientMap R x.1 := rfl

end ConstructionTargets.PolygonOuterOpenRestrictedQuotient
