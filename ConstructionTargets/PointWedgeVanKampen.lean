import ConstructionTargets.ThreeCirclesPathTopology
import ConstructionTargets.GenericTargetNaturalSourceReconstruction
import ConstructionTargets.PointedPuncturedCircleContraction
import ConstructionTargets.PointWedgeRestrictedOpenQuotient
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Point-wedge van Kampen foundation

This module is the stable entry point for the point-wedge van Kampen program.
The first banked milestone records the topology instances for the concrete
three-circle model.  The group-theoretic and van Kampen equivalences will be
added here without using the non-normalized counit component of
`TwoOpenFreeProductMapping.mapping`.
-/

open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace ConstructionTargets.PointWedgeVanKampen

open CategoryTheory
open PointedPuncturedCircleContraction
open PointWedgeQuotient PointWedgeRestrictedOpenQuotient

universe u

/-- An equivalence from a connected groupoid to a one-object groupoid induces
the expected equivalence on the automorphism group at any chosen object.  This
is the final, representation-independent step in the point-wedge van Kampen
construction. -/
def fundamentalGroupMulEquivOfSingleObjEquivalence
    {X : Type u} [TopologicalSpace X] (x : X) (G : Type u) [Group G]
    (E : FundamentalGroupoid X ≌ SingleObj G) :
    FundamentalGroup X x ≃* G :=
  (E.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk x)).trans
    ((Iso.conj (eqToIso (Subsingleton.elim
      (E.functor.obj (FundamentalGroupoid.mk x)) (SingleObj.star G)))).trans
      (SingleObj.toEnd G).symm)

/-- The three-circle model is locally path connected. -/
theorem threeCircles_locPathConnected :
    LocPathConnectedSpace ThreeCircles := inferInstance

/-- The three-circle model is path connected. -/
theorem threeCircles_pathConnected :
    PathConnectedSpace ThreeCircles := inferInstance

/-- The coproduct of two free groups is the free group on the sum of their
generating types. -/
def coprodFreeGroupEquivFreeGroupSum (α β : Type) :
    Monoid.Coprod (FreeGroup α) (FreeGroup β) ≃*
      FreeGroup (α ⊕ β) := by
  let forward : Monoid.Coprod (FreeGroup α) (FreeGroup β) →*
      FreeGroup (α ⊕ β) :=
    Monoid.Coprod.lift
      (FreeGroup.lift (fun a => FreeGroup.of (Sum.inl a)))
      (FreeGroup.lift (fun b => FreeGroup.of (Sum.inr b)))
  let backward : FreeGroup (α ⊕ β) →*
      Monoid.Coprod (FreeGroup α) (FreeGroup β) :=
    FreeGroup.lift (Sum.elim
      (fun a => Monoid.Coprod.inl (FreeGroup.of a))
      (fun b => Monoid.Coprod.inr (FreeGroup.of b)))
  have hleft : backward.comp forward = MonoidHom.id _ := by
    apply Monoid.Coprod.hom_ext
    · ext a
      change backward (forward (Monoid.Coprod.inl (FreeGroup.of a))) = _
      dsimp [forward, backward]
      exact FreeGroup.lift_apply_of
    · ext b
      change backward (forward (Monoid.Coprod.inr (FreeGroup.of b))) = _
      dsimp [forward, backward]
      exact FreeGroup.lift_apply_of
  have hright : forward.comp backward = MonoidHom.id _ := by
    ext s
    change forward (backward (FreeGroup.of s)) = _
    cases s with
    | inl a =>
      calc
        forward (backward (FreeGroup.of (Sum.inl a))) =
            forward (Monoid.Coprod.inl (FreeGroup.of a)) := by
              congr 1
        _ = FreeGroup.of (Sum.inl a) := by
          change (FreeGroup.lift (fun a : α => FreeGroup.of (Sum.inl a)))
            (FreeGroup.of a) = _
          exact FreeGroup.lift_apply_of
    | inr b =>
      calc
        forward (backward (FreeGroup.of (Sum.inr b))) =
            forward (Monoid.Coprod.inr (FreeGroup.of b)) := by
              congr 1
        _ = FreeGroup.of (Sum.inr b) := by
          change (FreeGroup.lift (fun b : β => FreeGroup.of (Sum.inr b)))
            (FreeGroup.of b) = _
          exact FreeGroup.lift_apply_of
  exact
    { toFun := forward
      invFun := backward
      left_inv := fun x => DFunLike.congr_fun hleft x
      right_inv := fun y => DFunLike.congr_fun hright y
      map_mul' := forward.map_mul }

/-- The generator equivalence `Fin 2 ⊕ Fin 1 ≃ Fin 3` transports the generic
free-group coproduct equivalence to the rank-three presentation. -/
def coprodFreeGroupFinTwoFinOne_equiv :
    Monoid.Coprod (FreeGroup (Fin 2)) (FreeGroup (Fin 1)) ≃*
      FreeGroup (Fin 3) :=
  (coprodFreeGroupEquivFreeGroupSum (Fin 2) (Fin 1)).trans
    (MulEquiv.ofBijective (FreeGroup.map finSumFinEquiv)
      ⟨FreeGroup.map_injective finSumFinEquiv.injective,
        FreeGroup.map_surjective finSumFinEquiv.surjective⟩)

/-- The integer coordinate on the rank-one free group, oriented from integers
to the free group for use after the circle winding-number equivalence. -/
def multiplicativeIntEquivFreeGroupFinOne :
    Multiplicative ℤ ≃* FreeGroup (Fin 1) :=
  (FreeGroup.mulEquivIntOfUnique (α := Fin 1)).symm

/-- The standard open neighbourhood of the circle basepoint, obtained by
removing the antipodal point. -/
def circleBaseNeighborhood : Set Circle :=
  {z | (z : ℂ) ≠ -1}

theorem circleBaseNeighborhood_isOpen : IsOpen circleBaseNeighborhood := by
  have hclosed : IsClosed {z : Circle | (z : ℂ) = -1} := by
    exact isClosed_singleton.preimage continuous_subtype_val
  simpa [circleBaseNeighborhood, Set.compl_setOf] using hclosed.isOpen_compl

theorem circleBase_mem : (1 : Circle) ∈ circleBaseNeighborhood := by
  norm_num [circleBaseNeighborhood]

/-- The stereographic straight-line contraction of the punctured circle,
viewed as a contraction of the literal open neighbourhood above. -/
def circleBaseNeighborhood_contraction :
    PointedContraction circleBaseNeighborhood ⟨1, circleBase_mem⟩ := by
  simpa only [circleBaseNeighborhood, puncturedCircleBase] using
    puncturedCirclePointedContraction

namespace PointedContraction

/-- Transport a pointed contraction backward through a homeomorphism. -/
def homeomorphSymm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} (e : X ≃ₜ Y) (h : PointedContraction Y (e x₀)) :
    PointedContraction X x₀ where
  homotopy :=
    { toFun := fun p => e.symm (h.homotopy (p.1, e p.2))
      continuous_toFun := e.symm.continuous.comp
        (h.homotopy.continuous.comp
          (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp }
  fixed := by
    intro t
    change e.symm (h.homotopy (t, e x₀)) = x₀
    rw [h.fixed]
    exact e.symm_apply_apply x₀

end PointedContraction

section WedgeContraction

universe v w

variable {X : Type v} {Y : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ : X} {y₀ : Y}

def wedgeContractSum (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) (t : unitInterval) :
    Sum X Y → Wedge x₀ y₀
  | .inl x => quotientMap x₀ y₀ (.inl (hX.homotopy (t, x)))
  | .inr y => quotientMap x₀ y₀ (.inr (hY.homotopy (t, y)))

private theorem wedgeContractSum_respects
    (hX : PointedContraction X x₀) (hY : PointedContraction Y y₀)
    (t : unitInterval) (a b : Sum X Y)
    (hab : Relation.EqvGen (Rel x₀ y₀) a b) :
    wedgeContractSum hX hY t a = wedgeContractSum hX hY t b := by
  induction hab with
  | rel a b hab =>
      cases hab
      change quotientMap x₀ y₀ (.inl (hX.homotopy (t, x₀))) =
        quotientMap x₀ y₀ (.inr (hY.homotopy (t, y₀)))
      rw [hX.fixed, hY.fixed]
      exact Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def wedgeContract (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) :
    unitInterval × Wedge x₀ y₀ → Wedge x₀ y₀ :=
  fun p => Quotient.lift (wedgeContractSum hX hY p.1)
    (wedgeContractSum_respects hX hY p.1) p.2

theorem wedgeContract_continuous (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) : Continuous (wedgeContract hX hY) := by
  have hq : Topology.IsQuotientMap (quotientMap x₀ y₀) :=
    isQuotientMap_quotient_mk'
  apply hq.continuous_lift_prod_right
  let g : (unitInterval × X) ⊕ (unitInterval × Y) → Wedge x₀ y₀
    | .inl p => quotientMap x₀ y₀ (.inl (hX.homotopy p))
    | .inr p => quotientMap x₀ y₀ (.inr (hY.homotopy p))
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    exact ⟨(continuous_quotientMap x₀ y₀).comp
      (continuous_inl.comp hX.homotopy.continuous),
      (continuous_quotientMap x₀ y₀).comp
        (continuous_inr.comp hY.homotopy.continuous)⟩
  have heq : (fun p : unitInterval × Sum X Y =>
      wedgeContract hX hY (p.1, quotientMap x₀ y₀ p.2)) =
      g ∘ Homeomorph.prodSumDistrib := by
    funext p
    rcases p with ⟨t, s⟩
    cases s <;> rfl
  rw [heq]
  exact hg.comp Homeomorph.prodSumDistrib.continuous

/-- Simultaneous pointed contractions on both summands descend to a pointed
contraction of their point wedge. -/
def wedgePointedContraction (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) :
    PointedContraction (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀)) where
  homotopy :=
    { toFun := wedgeContract hX hY
      continuous_toFun := wedgeContract_continuous hX hY
      map_zero_left := by
        rintro ⟨a⟩
        cases a with
        | inl x =>
            change quotientMap x₀ y₀ (Sum.inl (hX.homotopy (0, x))) =
              quotientMap x₀ y₀ (Sum.inl x)
            exact congrArg (fun z => quotientMap x₀ y₀ (Sum.inl z))
              (hX.homotopy.map_zero_left x)
        | inr y =>
            change quotientMap x₀ y₀ (Sum.inr (hY.homotopy (0, y))) =
              quotientMap x₀ y₀ (Sum.inr y)
            exact congrArg (fun z => quotientMap x₀ y₀ (Sum.inr z))
              (hY.homotopy.map_zero_left y)
      map_one_left := by
        rintro ⟨a⟩
        cases a with
        | inl x =>
            change quotientMap x₀ y₀ (Sum.inl (hX.homotopy (1, x))) =
              quotientMap x₀ y₀ (Sum.inl x₀)
            exact congrArg (fun z => quotientMap x₀ y₀ (Sum.inl z))
              (hX.homotopy.map_one_left x)
        | inr y =>
            calc
              quotientMap x₀ y₀ (.inr (hY.homotopy (1, y))) =
                  quotientMap x₀ y₀ (.inr y₀) := congrArg
                    (fun z => quotientMap x₀ y₀ (.inr z))
                    (hY.homotopy.map_one_left y)
              _ = quotientMap x₀ y₀ (.inl x₀) := (Quotient.sound
                    (Relation.EqvGen.rel _ _ Rel.base)).symm }
  fixed := by
    intro t
    change quotientMap x₀ y₀ (.inl (hX.homotopy (t, x₀))) = _
    rw [hX.fixed]

end WedgeContraction

/-- The restricted open neighbourhood of the basepoint in the two-circle
wedge. -/
def twoCirclesBaseNeighborhood : Set TwoCircles :=
  restrictedOpen (1 : Circle) (1 : Circle)
    circleBaseNeighborhood circleBaseNeighborhood

theorem twoCirclesBaseNeighborhood_isOpen :
    IsOpen twoCirclesBaseNeighborhood :=
  restrictedOpen_isOpen circleBaseNeighborhood_isOpen
    circleBaseNeighborhood_isOpen circleBase_mem circleBase_mem

theorem twoCirclesBase_mem :
    twoCirclesPoint ∈ twoCirclesBaseNeighborhood := by
  exact ⟨.inl (1 : Circle), circleBase_mem, rfl⟩

def twoCirclesBaseNeighborhoodHomeomorph :
    twoCirclesBaseNeighborhood ≃ₜ
      Wedge (⟨1, circleBase_mem⟩ : circleBaseNeighborhood)
        (⟨1, circleBase_mem⟩ : circleBaseNeighborhood) :=
  restrictedOpenHomeomorphWedge circleBaseNeighborhood_isOpen
    circleBaseNeighborhood_isOpen circleBase_mem circleBase_mem

theorem twoCirclesBaseNeighborhoodHomeomorph_base :
    twoCirclesBaseNeighborhoodHomeomorph
      ⟨twoCirclesPoint, twoCirclesBase_mem⟩ =
        quotientMap (⟨1, circleBase_mem⟩ : circleBaseNeighborhood)
          (⟨1, circleBase_mem⟩ : circleBaseNeighborhood)
          (.inl ⟨1, circleBase_mem⟩) := by
  exact restrictedOpenHomeomorphWedge_left _ _ _ _ _ _

/-- The simultaneous contraction of the two punctured-circle legs,
transported back to the literal restricted open neighbourhood. -/
def twoCirclesBaseNeighborhood_contraction :
    PointedContraction twoCirclesBaseNeighborhood
      ⟨twoCirclesPoint, twoCirclesBase_mem⟩ := by
  let e := twoCirclesBaseNeighborhoodHomeomorph
  let h := wedgePointedContraction circleBaseNeighborhood_contraction
    circleBaseNeighborhood_contraction
  have he : e ⟨twoCirclesPoint, twoCirclesBase_mem⟩ =
      quotientMap (⟨1, circleBase_mem⟩ : circleBaseNeighborhood)
        (⟨1, circleBase_mem⟩ : circleBaseNeighborhood)
        (.inl ⟨1, circleBase_mem⟩) :=
    twoCirclesBaseNeighborhoodHomeomorph_base
  rw [← he] at h
  exact ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm e h

#print axioms threeCircles_locPathConnected
#print axioms fundamentalGroupMulEquivOfSingleObjEquivalence
#print axioms threeCircles_pathConnected
#print axioms coprodFreeGroupEquivFreeGroupSum
#print axioms coprodFreeGroupFinTwoFinOne_equiv
#print axioms multiplicativeIntEquivFreeGroupFinOne
#print axioms circleBaseNeighborhood_contraction
#print axioms twoCirclesBaseNeighborhood_contraction

end ConstructionTargets.PointWedgeVanKampen
