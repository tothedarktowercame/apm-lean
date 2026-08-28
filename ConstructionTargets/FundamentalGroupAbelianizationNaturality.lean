import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Naturality of fundamental-group abelianization

This is the algebraic half of the degree-one Hurewicz comparison.  It does
not identify the abelianization with singular first homology.
-/

noncomputable section

namespace ConstructionTargets.FundamentalGroupAbelianizationNaturality

variable {X Y Z A : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The map on abelianized fundamental groups induced by a continuous map. -/
def fundamentalGroupAbelianizationMap (f : C(X, Y)) (x : X) :
    Abelianization (FundamentalGroup X x) →*
      Abelianization (FundamentalGroup Y (f x)) :=
  Abelianization.map (FundamentalGroup.map f x)

@[simp] theorem fundamentalGroupAbelianizationMap_of
    (f : C(X, Y)) (x : X) (p : FundamentalGroup X x) :
    fundamentalGroupAbelianizationMap f x (Abelianization.of p) =
      Abelianization.of (FundamentalGroup.map f x p) := rfl

/-- Abelianized fundamental-group maps compose functorially. -/
theorem fundamentalGroupAbelianizationMap_comp
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    (fundamentalGroupAbelianizationMap g (f x)).comp
        (fundamentalGroupAbelianizationMap f x) =
      fundamentalGroupAbelianizationMap (g.comp f) x := by
  apply Abelianization.hom_ext
  ext p
  change Abelianization.of
      ((FundamentalGroup.map g (f x)) ((FundamentalGroup.map f x) p)) =
    Abelianization.of ((FundamentalGroup.map (g.comp f) x) p)
  apply congrArg Abelianization.of
  change (FundamentalGroupoid.map g).map
      ((FundamentalGroupoid.map f).map p) =
    (FundamentalGroupoid.map (g.comp f)).map p
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- A homomorphism from the target fundamental group to any commutative group
commutes with the induced abelianization map after applying the universal
abelianization lift. -/
theorem abelianizationLift_comp_fundamentalGroupAbelianizationMap
    [CommGroup A] (f : C(X, Y)) (x : X)
    (phi : FundamentalGroup Y (f x) →* A) :
    (Abelianization.lift phi).comp (fundamentalGroupAbelianizationMap f x) =
      Abelianization.lift (phi.comp (FundamentalGroup.map f x)) := by
  apply Abelianization.hom_ext
  ext p
  rfl

/-- Equality of homomorphisms on fundamental groups gives equality after
passing to abelianizations. -/
theorem fundamentalGroupAbelianizationMap_eq_of_map_eq
    (f g : C(X, Y)) (x : X) (hpoint : f x = g x)
    (hmap : FundamentalGroup.mapOfEq f hpoint = FundamentalGroup.map g x) :
    Abelianization.map (FundamentalGroup.mapOfEq f hpoint) =
      fundamentalGroupAbelianizationMap g x := by
  rw [hmap]
  rfl

#print axioms fundamentalGroupAbelianizationMap_comp
#print axioms abelianizationLift_comp_fundamentalGroupAbelianizationMap
#print axioms fundamentalGroupAbelianizationMap_eq_of_map_eq

end ConstructionTargets.FundamentalGroupAbelianizationNaturality
