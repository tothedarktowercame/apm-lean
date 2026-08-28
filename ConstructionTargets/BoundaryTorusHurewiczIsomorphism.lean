import ConstructionTargets.CircleHurewiczIsomorphism
import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.BoundaryTorusIntegralHomologyComplete
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The degree-one Hurewicz isomorphism for the boundary torus
-/

noncomputable section

namespace ConstructionTargets.BoundaryTorusHurewiczIsomorphism

open CategoryTheory
open ConstructionTargets.CircleHomology
open ConstructionTargets.CircleUniversalCover
open ConstructionTargets.CircleHurewiczIsomorphism
open ConstructionTargets.FundamentalGroupProduct
open ConstructionTargets.DegreeOneHurewiczMap
open ConstructionTargets.DegreeOneHurewiczSurjective
open ConstructionTargets.BoundaryTorusIntegralHomologyComplete

/-- A surjective endomorphism of a finite-rank free integral module is
injective. -/
theorem finIntLinearMap_injective_of_surjective {n : ℕ}
    (f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (hf : Function.Surjective f) : Function.Injective f :=
  Module.End.injective_of_surjective ℤ (Fin n → ℤ) hf

/-- Additive formulation of finite-free Hopficity. -/
theorem finIntAddMonoidHom_injective_of_surjective {n : ℕ}
    (f : (Fin n → ℤ) →+ (Fin n → ℤ))
    (hf : Function.Surjective f) : Function.Injective f :=
  finIntLinearMap_injective_of_surjective f.toIntLinearMap hf

/-- Multiplicative formulation used for fundamental groups. -/
theorem multiplicative_finInt_monoidHom_injective_of_surjective {n : ℕ}
    (f : Multiplicative (Fin n → ℤ) →* Multiplicative (Fin n → ℤ))
    (hf : Function.Surjective f) : Function.Injective f := by
  let fa : (Fin n → ℤ) →+ (Fin n → ℤ) :=
    { toFun := fun z => Multiplicative.toAdd (f (Multiplicative.ofAdd z))
      map_zero' := f.map_one
      map_add' := f.map_mul }
  exact finIntAddMonoidHom_injective_of_surjective fa hf

private abbrev SphereOne := ConstructionTargets.SphereHomology.Sphere 1
private abbrev BT := ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus

def boundaryTorusBasepoint : BT :=
  (1, circleHomeomorphSphereOne 1)

/-- A homeomorphism induces an equivalence of the based fundamental groups. -/
def fundamentalGroupMulEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) where
  toFun := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_apply x)
  left_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.map_apply]
      change (FundamentalGroup.mapOfEq _ _)
        (Path.Homotopic.Quotient.mk (p.map e.continuous)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.symm_apply_apply (p t)
  right_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.apply_symm_apply (p t)
  map_mul' := map_mul _

local instance circlePathConnectedSpace : PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have h : IsPathConnected
        (circleHomeomorphSphereOne ⁻¹' (Set.univ : Set SphereOne)) :=
      circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using h)

local instance sphereOnePathConnectedSpace : PathConnectedSpace SphereOne :=
  pathConnectedSpace_iff_univ.mpr (by
    have h : IsPathConnected (circleHomeomorphSphereOne '' Set.univ) :=
      circleHomeomorphSphereOne.isPathConnected_image.mpr isPathConnected_univ
    simpa using h)

local instance boundaryTorusPathConnectedSpace : PathConnectedSpace BT :=
  ⟨⟨boundaryTorusBasepoint⟩, fun x y =>
    ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1)
      (PathConnectedSpace.somePath x.2 y.2)⟩⟩

private def intProdMulEquivFinTwo :
    Multiplicative ℤ × Multiplicative ℤ ≃*
      Multiplicative (Fin 2 → ℤ) :=
  (MulEquiv.prodMultiplicative ℤ ℤ).symm.trans
    (AddEquiv.toMultiplicative
      (LinearEquiv.piFinTwo ℤ (fun _ : Fin 2 => ℤ)).symm.toAddEquiv)

/-- The fundamental group of the concrete boundary torus, in its two winding
coordinates. -/
def boundaryTorusFundamentalGroupMulEquivFinTwo :
    FundamentalGroup BT boundaryTorusBasepoint ≃*
      Multiplicative (Fin 2 → ℤ) :=
  (fundamentalGroupProdMulEquiv (1 : Circle)
      (circleHomeomorphSphereOne 1)).trans
    (circleFundamentalGroupMulEquivInt.prodCongr
      ((fundamentalGroupMulEquivOfHomeomorph circleHomeomorphSphereOne 1).symm.trans
        circleFundamentalGroupMulEquivInt)) |>.trans
    intProdMulEquivFinTwo

/-- Abelianized boundary-torus fundamental group in its two winding
coordinates. -/
def boundaryTorusAbelianizedFundamentalGroupMulEquivFinTwo :
    Abelianization (FundamentalGroup BT boundaryTorusBasepoint) ≃*
      Multiplicative (Fin 2 → ℤ) :=
  boundaryTorusFundamentalGroupMulEquivFinTwo.abelianizationCongr.trans
    (commGroupAbelianizationMulEquiv (Multiplicative (Fin 2 → ℤ)))

/-- The compiled boundary-torus H1 coordinate as an additive equivalence. -/
def boundaryTorusH1AddEquivFinTwo : IntegralH1 BT ≃+ (Fin 2 → ℤ) where
  toFun := boundaryTorusH1GroupIsoFinTwo.hom
  invFun := boundaryTorusH1GroupIsoFinTwo.inv
  left_inv := boundaryTorusH1GroupIsoFinTwo.hom_inv_id_apply
  right_inv := boundaryTorusH1GroupIsoFinTwo.inv_hom_id_apply
  map_add' := boundaryTorusH1GroupIsoFinTwo.hom.hom.map_add

def boundaryTorusH1MulEquivFinTwo :
    Multiplicative (IntegralH1 BT) ≃* Multiplicative (Fin 2 → ℤ) :=
  AddEquiv.toMultiplicative boundaryTorusH1AddEquivFinTwo

/-- Boundary-torus Hurewicz conjugated by winding and integral-H1
coordinates. -/
def boundaryTorusHurewiczFinTwoCoordinate :
    Multiplicative (Fin 2 → ℤ) →* Multiplicative (Fin 2 → ℤ) :=
  boundaryTorusH1MulEquivFinTwo.toMonoidHom.comp
    ((abelianizedFundamentalGroupToH1 boundaryTorusBasepoint).comp
      boundaryTorusAbelianizedFundamentalGroupMulEquivFinTwo.symm.toMonoidHom)

theorem boundaryTorusHurewiczFinTwoCoordinate_surjective :
    Function.Surjective boundaryTorusHurewiczFinTwoCoordinate :=
  boundaryTorusH1MulEquivFinTwo.surjective.comp
    ((abelianizedFundamentalGroupToH1_surjective boundaryTorusBasepoint).comp
      boundaryTorusAbelianizedFundamentalGroupMulEquivFinTwo.symm.surjective)

theorem boundaryTorusHurewiczFinTwoCoordinate_injective :
    Function.Injective boundaryTorusHurewiczFinTwoCoordinate :=
  multiplicative_finInt_monoidHom_injective_of_surjective _
    boundaryTorusHurewiczFinTwoCoordinate_surjective

/-- Boundary-torus-specific degree-one Hurewicz isomorphism after
abelianization. -/
def boundaryTorusAbelianizedFundamentalGroupH1MulEquiv :
    Abelianization (FundamentalGroup BT boundaryTorusBasepoint) ≃*
      Multiplicative (IntegralH1 BT) :=
  MulEquiv.ofBijective
    (abelianizedFundamentalGroupToH1 boundaryTorusBasepoint) (by
      constructor
      · intro x y h
        apply boundaryTorusAbelianizedFundamentalGroupMulEquivFinTwo.injective
        apply boundaryTorusHurewiczFinTwoCoordinate_injective
        simpa [boundaryTorusHurewiczFinTwoCoordinate] using
          congrArg boundaryTorusH1MulEquivFinTwo h
      · exact abelianizedFundamentalGroupToH1_surjective boundaryTorusBasepoint)

#print axioms finIntLinearMap_injective_of_surjective
#print axioms fundamentalGroupMulEquivOfHomeomorph
#print axioms boundaryTorusFundamentalGroupMulEquivFinTwo
#print axioms boundaryTorusHurewiczFinTwoCoordinate_injective
#print axioms boundaryTorusAbelianizedFundamentalGroupH1MulEquiv

end ConstructionTargets.BoundaryTorusHurewiczIsomorphism
