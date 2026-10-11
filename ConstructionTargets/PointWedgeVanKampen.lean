import ConstructionTargets.ThreeCirclesPathTopology
import ConstructionTargets.GenericTargetNaturalSourceReconstruction
import ConstructionTargets.PointedPuncturedCircleContraction
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

#print axioms threeCircles_locPathConnected
#print axioms fundamentalGroupMulEquivOfSingleObjEquivalence
#print axioms threeCircles_pathConnected
#print axioms coprodFreeGroupEquivFreeGroupSum
#print axioms coprodFreeGroupFinTwoFinOne_equiv
#print axioms multiplicativeIntEquivFreeGroupFinOne
#print axioms circleBaseNeighborhood_contraction

end ConstructionTargets.PointWedgeVanKampen
