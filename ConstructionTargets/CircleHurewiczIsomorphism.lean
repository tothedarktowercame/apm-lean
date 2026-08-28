import ConstructionTargets.DegreeOneHurewiczSurjective
import ConstructionTargets.CircleUniversalCover
import ConstructionTargets.BoundaryTorusMayerVietoris

/-!
# The degree-one Hurewicz isomorphism for the circle

This file proves only the rank-one case.  It coordinates the abelianized
fundamental group and integral first homology by `ℤ`, and uses surjectivity to
deduce injectivity of the resulting integer endomorphism.
-/

noncomputable section

namespace ConstructionTargets.CircleHurewiczIsomorphism

open CategoryTheory
open ConstructionTargets.CircleUniversalCover
open ConstructionTargets.DegreeOneHurewiczMap
open ConstructionTargets.DegreeOneHurewiczSurjective
open ConstructionTargets.BoundaryTorusMayerVietoris

local instance circlePathConnectedSpace : PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have h : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using h)

/-- Abelianizing an already commutative group changes no information. -/
def commGroupAbelianizationMulEquiv (G : Type) [CommGroup G] :
    Abelianization G ≃* G :=
  MulEquiv.ofBijective (Abelianization.lift (MonoidHom.id G)) (by
    constructor
    · intro x y h
      induction x using QuotientGroup.induction_on with
      | _ a =>
        induction y using QuotientGroup.induction_on with
        | _ b =>
          exact congrArg Abelianization.of h
    · intro g
      exact ⟨Abelianization.of g, Abelianization.lift_apply_of _ _⟩)

/-- The abelianized fundamental group of the circle, in its winding-number
coordinate. -/
def circleAbelianizedFundamentalGroupMulEquivInt :
    Abelianization (FundamentalGroup Circle 1) ≃* Multiplicative ℤ :=
  circleFundamentalGroupMulEquivInt.abelianizationCongr.trans
    (commGroupAbelianizationMulEquiv (Multiplicative ℤ))

/-- The existing integral circle-H1 coordinate, exposed as an additive
equivalence of underlying groups. -/
def circleH1AddEquivInt : IntegralH1 Circle ≃+ ℤ where
  toFun := circleH1GroupIsoInt.hom
  invFun := circleH1GroupIsoInt.inv
  left_inv := circleH1GroupIsoInt.hom_inv_id_apply
  right_inv := circleH1GroupIsoInt.inv_hom_id_apply
  map_add' := circleH1GroupIsoInt.hom.hom.map_add

def circleH1MulEquivInt :
    Multiplicative (IntegralH1 Circle) ≃* Multiplicative ℤ :=
  AddEquiv.toMultiplicative circleH1AddEquivInt

/-- A surjective additive endomorphism of `ℤ` is injective. -/
theorem int_addMonoidHom_injective_of_surjective (f : ℤ →+ ℤ)
    (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨c, hc⟩ := hf 1
  have hformula (n : ℤ) : f n = n * f 1 := by
    simpa [smul_eq_mul] using map_zsmul f n (1 : ℤ)
  intro a b hab
  rw [hformula c] at hc
  rw [hformula a, hformula b] at hab
  calc
    a = a * 1 := by ring
    _ = a * (c * f 1) := by rw [hc]
    _ = c * (a * f 1) := by ring
    _ = c * (b * f 1) := by rw [hab]
    _ = b * (c * f 1) := by ring
    _ = b * 1 := by rw [hc]
    _ = b := by ring

/-- Multiplicative version of the rank-one algebra lemma. -/
theorem multiplicative_int_monoidHom_injective_of_surjective
    (f : Multiplicative ℤ →* Multiplicative ℤ)
    (hf : Function.Surjective f) : Function.Injective f := by
  let fa : ℤ →+ ℤ :=
    { toFun := fun n => Multiplicative.toAdd (f (Multiplicative.ofAdd n))
      map_zero' := f.map_one
      map_add' := f.map_mul }
  exact int_addMonoidHom_injective_of_surjective fa hf

/-- The circle Hurewicz map conjugated into winding and H1 integer
coordinates. -/
def circleHurewiczIntegerCoordinate : Multiplicative ℤ →* Multiplicative ℤ :=
  circleH1MulEquivInt.toMonoidHom.comp
    ((abelianizedFundamentalGroupToH1 (1 : Circle)).comp
      circleAbelianizedFundamentalGroupMulEquivInt.symm.toMonoidHom)

theorem circleHurewiczIntegerCoordinate_surjective :
    Function.Surjective circleHurewiczIntegerCoordinate := by
  exact circleH1MulEquivInt.surjective.comp
    ((abelianizedFundamentalGroupToH1_surjective (1 : Circle)).comp
      circleAbelianizedFundamentalGroupMulEquivInt.symm.surjective)

theorem circleHurewiczIntegerCoordinate_injective :
    Function.Injective circleHurewiczIntegerCoordinate :=
  multiplicative_int_monoidHom_injective_of_surjective _
    circleHurewiczIntegerCoordinate_surjective

/-- Circle-specific degree-one Hurewicz isomorphism after abelianization. -/
def circleAbelianizedFundamentalGroupH1MulEquiv :
    Abelianization (FundamentalGroup Circle 1) ≃*
      Multiplicative (IntegralH1 Circle) :=
  MulEquiv.ofBijective (abelianizedFundamentalGroupToH1 (1 : Circle)) (by
    constructor
    · intro x y h
      apply circleAbelianizedFundamentalGroupMulEquivInt.injective
      apply circleHurewiczIntegerCoordinate_injective
      simpa [circleHurewiczIntegerCoordinate] using
        congrArg circleH1MulEquivInt h
    · exact abelianizedFundamentalGroupToH1_surjective (1 : Circle))

#print axioms commGroupAbelianizationMulEquiv
#print axioms int_addMonoidHom_injective_of_surjective
#print axioms circleHurewiczIntegerCoordinate_injective
#print axioms circleAbelianizedFundamentalGroupH1MulEquiv

end ConstructionTargets.CircleHurewiczIsomorphism
