import ConstructionTargets.RadialQuotientOpenSets

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonRadialOpenCover

open ConstructionTargets.Surfaces
open ConstructionTargets.RadialQuotientOpenSets

variable (R : Disk → Disk → Prop)

abbrev PolygonQuotient := Quotient (Relation.EqvGen.setoid R)

def radius (x : Disk) : ℝ := ‖(x : ℂ)‖

def innerSource : Set Disk := radius ⁻¹' Set.Iio (3 / 4 : ℝ)
def outerSource : Set Disk := radius ⁻¹' Set.Ioi (1 / 4 : ℝ)
def overlapSource : Set Disk := innerSource ∩ outerSource

def quotientMap : Disk → PolygonQuotient R :=
  fun x => Quotient.mk _ x

def innerOpen : Set (PolygonQuotient R) := quotientMap R '' innerSource
def outerOpen : Set (PolygonQuotient R) := quotientMap R '' outerSource
def overlapOpen : Set (PolygonQuotient R) := quotientMap R '' overlapSource

theorem continuous_radius : Continuous radius :=
  continuous_norm.comp continuous_subtype_val

theorem innerSource_isOpen : IsOpen innerSource :=
  continuous_radius.isOpen_preimage _ isOpen_Iio

theorem outerSource_isOpen : IsOpen outerSource :=
  continuous_radius.isOpen_preimage _ isOpen_Ioi

theorem innerOpen_isOpen
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    IsOpen (innerOpen R) := by
  exact isOpen_radial_image R radius continuous_radius hR _ isOpen_Iio

theorem outerOpen_isOpen
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    IsOpen (outerOpen R) := by
  exact isOpen_radial_image R radius continuous_radius hR _ isOpen_Ioi

theorem innerOpen_union_outerOpen : innerOpen R ∪ outerOpen R = Set.univ := by
  ext z
  constructor
  · intro; trivial
  · intro
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective z
    by_cases hx : radius x < 3 / 4
    · exact Or.inl ⟨x, hx, rfl⟩
    · right
      refine ⟨x, ?_, rfl⟩
      change 1 / 4 < radius x
      have hx' : 3 / 4 ≤ radius x := le_of_not_gt hx
      linarith

theorem overlapOpen_eq_inter
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    overlapOpen R = innerOpen R ∩ outerOpen R := by
  ext z
  constructor
  · rintro ⟨x, ⟨hxI, hxO⟩, rfl⟩
    exact ⟨⟨x, hxI, rfl⟩, ⟨x, hxO, rfl⟩⟩
  · rintro ⟨⟨x, hxI, hxz⟩, ⟨y, hyO, hyz⟩⟩
    have hxy : Relation.EqvGen R x y := Quotient.exact (hxz.trans hyz.symm)
    have hr : radius x = radius y :=
      eqvGen_preserves_of_rel_preserves R radius hR hxy
    refine ⟨x, ⟨hxI, ?_⟩, hxz⟩
    change 1 / 4 < radius x
    change 1 / 4 < radius y at hyO
    rwa [hr]

structure Package (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) where
  inner_isOpen : IsOpen (innerOpen R)
  outer_isOpen : IsOpen (outerOpen R)
  cover : innerOpen R ∪ outerOpen R = Set.univ
  overlap : overlapOpen R = innerOpen R ∩ outerOpen R

def package (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) : Package R hR where
  inner_isOpen := innerOpen_isOpen R hR
  outer_isOpen := outerOpen_isOpen R hR
  cover := innerOpen_union_outerOpen R
  overlap := overlapOpen_eq_inter R hR

theorem surfaceRel_radius_eq (orientable : Bool) (genus : ℕ)
    {x y : Disk} (h : SurfaceRel orientable genus x y) :
    radius x = radius y := by
  simpa [radius] using surfaceRel_norm_eq orientable genus h

def surfacePackage (orientable : Bool) (genus : ℕ) :
    Package (SurfaceRel orientable genus)
      (fun {_ _} h => surfaceRel_radius_eq orientable genus h) :=
  package _ (fun {_ _} h => surfaceRel_radius_eq orientable genus h)

end ConstructionTargets.PolygonRadialOpenCover
