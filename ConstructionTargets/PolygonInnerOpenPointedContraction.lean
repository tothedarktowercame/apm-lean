import ConstructionTargets.PolygonBoundaryThreeCirclesLiteralFormulas
import ConstructionTargets.PointedPuncturedCircleContraction
import ConstructionTargets.PolygonOuterOpenRestrictedQuotient

open Set Topology
open unitInterval
noncomputable section

namespace ConstructionTargets.PolygonInnerOpenPointedContraction

open Surfaces
open RadialQuotientOpenSets
open PolygonRadialOpenCover
open PolygonOuterRadialRelation
open PolygonTorusCrosscapRelation
open PointedPuncturedCircleContraction

variable (R : Disk → Disk → Prop)

def innerBase : innerOpen R := by
  refine ⟨quotientMap R (0 : Disk), ?_⟩
  exact ⟨0, by norm_num [innerSource, radius], rfl⟩

theorem quotientMap_preimage_innerOpen
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    quotientMap R ⁻¹' innerOpen R = innerSource := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have he : Relation.EqvGen R y x := Quotient.exact hxy
    have hr : radius y = radius x :=
      eqvGen_preserves_of_rel_preserves R radius hR he
    change radius x < 3 / 4
    change radius y < 3 / 4 at hy
    linarith
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem eq_of_eqvGen_of_inner
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    {x y : Disk} (h : Relation.EqvGen R x y) (hx : radius x < 3 / 4) : x = y := by
  induction h with
  | rel x y hxy =>
      have hb := (hboundary hxy).1
      linarith
  | refl x => rfl
  | symm x y h ih =>
      have hr : radius _ = radius _ :=
        eqvGen_preserves_of_rel_preserves R radius hR h
      exact (ih (by linarith)).symm
  | trans x y z h₁ h₂ ih₁ ih₂ =>
      have hxy := ih₁ hx
      subst y
      exact ih₂ hx

abbrev InnerPreimage := {x : Disk // quotientMap R x ∈ innerOpen R}

def restrictedInnerQuotientMap : InnerPreimage R → innerOpen R :=
  (innerOpen R).restrictPreimage (quotientMap R)

theorem restrictedInnerQuotientMap_isQuotientMap
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    IsQuotientMap (restrictedInnerQuotientMap R) := by
  exact isQuotientMap_quotient_mk'.restrictPreimage_isOpen
    (innerOpen_isOpen R hR)

theorem restrictedInnerQuotientMap_injective
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    Function.Injective (restrictedInnerQuotientMap R) := by
  intro x y hxy
  apply Subtype.ext
  apply eq_of_eqvGen_of_inner R hR hboundary (Quotient.exact (congrArg Subtype.val hxy))
  have hx : x.1 ∈ innerSource := by
    rw [← quotientMap_preimage_innerOpen R hR]
    exact x.2
  exact hx

def innerPreimageHomeomorph
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    InnerPreimage R ≃ₜ innerOpen R := by
  let q := restrictedInnerQuotientMap R
  have hq := restrictedInnerQuotientMap_isQuotientMap R hR
  have hi := restrictedInnerQuotientMap_injective R hR hboundary
  let e : InnerPreimage R ≃ innerOpen R := Equiv.ofBijective q ⟨hi, hq.surjective⟩
  exact
    { e with
      continuous_toFun := hq.continuous
      continuous_invFun := hq.continuous_iff.2 (by
        simpa [e, q, Function.comp_def] using continuous_id) }

def innerScale
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (t : I) (x : InnerPreimage R) : InnerPreimage R := by
  let a : ℝ := 1 - (t : ℝ)
  let z : ℂ := a • (x.1.1 : ℂ)
  have ha0 : 0 ≤ a := sub_nonneg.mpr t.2.2
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [t.2.1]
  have hz : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [z]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
    have hxDisk : ‖(x.1.1 : ℂ)‖ ≤ 1 := by
      have := x.1.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    calc a * ‖(x.1.1 : ℂ)‖ ≤ 1 * ‖(x.1.1 : ℂ)‖ := by gcongr
         _ ≤ 1 := by simpa using hxDisk
  refine ⟨⟨z, hz⟩, ?_⟩
  change ⟨z, hz⟩ ∈ quotientMap R ⁻¹' innerOpen R
  rw [quotientMap_preimage_innerOpen R hR]
  change ‖z‖ < 3 / 4
  have hxmem : x.1 ∈ innerSource := by
    rw [← quotientMap_preimage_innerOpen R hR]
    exact x.2
  have hx : radius x.1 < 3 / 4 := hxmem
  dsimp [radius] at hx ⊢
  dsimp [z]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  calc a * ‖(x.1.1 : ℂ)‖ ≤ 1 * ‖(x.1.1 : ℂ)‖ := by gcongr
       _ < 3 / 4 := by simpa using hx

theorem continuous_innerScale
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) :
    Continuous (fun p : I × InnerPreimage R => innerScale R hR p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun p : I × InnerPreimage R =>
    ((1 - (p.1 : ℝ) : ℝ) : ℂ) * (p.2.1.1 : ℂ))
  fun_prop

@[simp] theorem innerScale_zero
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) (x : InnerPreimage R) :
    innerScale R hR 0 x = x := by
  apply Subtype.ext
  apply Subtype.ext
  simp [innerScale]

def innerZero : InnerPreimage R := by
  refine ⟨0, ?_⟩
  exact ⟨0, by norm_num [innerSource, radius], rfl⟩

@[simp] theorem innerScale_one
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) (x : InnerPreimage R) :
    innerScale R hR 1 x = innerZero R := by
  apply Subtype.ext
  apply Subtype.ext
  simp [innerScale, innerZero]

@[simp] theorem innerScale_innerZero
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y) (t : I) :
    innerScale R hR t (innerZero R) = innerZero R := by
  apply Subtype.ext
  apply Subtype.ext
  simp [innerScale, innerZero]

def innerOpenHomotopy
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    I × innerOpen R → innerOpen R := fun p =>
  innerPreimageHomeomorph R hR hboundary
    (innerScale R hR p.1 ((innerPreimageHomeomorph R hR hboundary).symm p.2))

theorem continuous_innerOpenHomotopy
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    Continuous (innerOpenHomotopy R hR hboundary) := by
  apply (innerPreimageHomeomorph R hR hboundary).continuous.comp
  simpa only [Function.comp_apply] using (continuous_innerScale R hR).comp
    (continuous_fst.prodMk
      ((innerPreimageHomeomorph R hR hboundary).symm.continuous.comp continuous_snd))

@[simp] theorem innerPreimageHomeomorph_innerZero
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    innerPreimageHomeomorph R hR hboundary (innerZero R) = innerBase R := by
  rfl

@[simp] theorem innerPreimageHomeomorph_symm_innerBase
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    (innerPreimageHomeomorph R hR hboundary).symm (innerBase R) = innerZero R := by
  apply (innerPreimageHomeomorph R hR hboundary).injective
  simp

def innerOpenPointedContraction
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    PointedContraction (innerOpen R) (innerBase R) where
  homotopy :=
    { toFun := innerOpenHomotopy R hR hboundary
      continuous_toFun := continuous_innerOpenHomotopy R hR hboundary
      map_zero_left := by
        intro z
        simp [innerOpenHomotopy]
      map_one_left := by
        intro z
        simp [innerOpenHomotopy]
    }
  fixed := by
    intro t
    change innerOpenHomotopy R hR hboundary (t, innerBase R) = innerBase R
    simp [innerOpenHomotopy]

def n3InnerOpenPointedContraction :
    PointedContraction (innerOpen (SurfaceRel false 3))
      (innerBase (SurfaceRel false 3)) :=
  innerOpenPointedContraction _
    (fun {_ _} h => surfaceRel_radius_eq false 3 h)
    (fun {_ _} h => surfaceRel_boundary false 3 h)

def torusCrosscapInnerOpenPointedContraction :
    PointedContraction (innerOpen TorusCrosscapRel)
      (innerBase TorusCrosscapRel) :=
  innerOpenPointedContraction _
    (fun {_ _} h => by simpa [radius] using torusCrosscapRel_norm_eq h)
    (fun {_ _} h => torusCrosscapRel_boundary h)

end ConstructionTargets.PolygonInnerOpenPointedContraction
