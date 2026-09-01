import ConstructionTargets.TorusCircleWedgeOpenCover
import ConstructionTargets.GenericSpanPseudoCoconeTransport
import ConstructionTargets.TwoOpenFundamentalGroupoidSpan
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

open Set CategoryTheory
open scoped ContinuousMap
noncomputable section

namespace ConstructionTargets.TorusCircleWedgeFundamentalGroupoidSpan

open ConstructionTargets.TorusCircleWedgeOpenCover
open ConstructionTargets.TwoOpenFundamentalGroupoidSpan
open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.PointWedgePointedContractionDescent
open ConstructionTargets.PointedPuncturedCircleContraction
open ConstructionTargets.GenericSpanPseudoCoconeTransport

abbrev W := GenericWedge
abbrev UV := {z : W // z ∈ U ∩ V}

def actualLeft : Functor (FundamentalGroupoid UV) (FundamentalGroupoid U) :=
  overlapFundamentalGroupoidMap (X := W) (U := U) (V := V) true

def actualRight : Functor (FundamentalGroupoid UV) (FundamentalGroupoid V) :=
  overlapFundamentalGroupoidMap (X := W) (U := U) (V := V) false

def leftConst : C(Unit, Torus) := ContinuousMap.const Unit ((1, 1) : Torus)
def rightConst : C(Unit, Circle) := ContinuousMap.const Unit (1 : Circle)

def coordinateLeft : Functor (FundamentalGroupoid Unit) (FundamentalGroupoid Torus) :=
  FundamentalGroupoid.map leftConst

def coordinateRight : Functor (FundamentalGroupoid Unit) (FundamentalGroupoid Circle) :=
  FundamentalGroupoid.map rightConst

def overlapBase : UV :=
  ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl (1, 1)),
    ⟨⟨.inl (1, 1), trivial, rfl⟩,
      ⟨.inl (1, 1), one_one_mem_N, rfl⟩⟩⟩

theorem UVHomotopyEquiv_invFun_unit :
    UVHomotopyEquiv.invFun () = overlapBase := by
  change UVModel.symm
      (quotientMap (puncturedCircleBase, puncturedCircleBase)
        puncturedCircleBase (.inl (puncturedCircleBase, puncturedCircleBase))) =
    overlapBase
  apply UVModel.injective
  rw [UVModel.apply_symm_apply]
  simpa [overlapBase] using
    (UVModel_left ((1, 1) : Torus) one_one_mem_N).symm

theorem left_coordinate_map_strict :
    UHomotopyEquiv.toFun.comp
      ((overlapToPiece (X := W) (U := U) (V := V) true).comp
        UVHomotopyEquiv.invFun) = leftConst := by
  apply ContinuousMap.ext
  intro u
  cases u
  change UHomotopyEquiv.toFun
      (overlapToPiece (X := W) (U := U) (V := V) true
        (UVHomotopyEquiv.invFun ())) = ((1, 1) : Torus)
  rw [UVHomotopyEquiv_invFun_unit]
  change (wedgeHomotopyEquivLeft puncturedCirclePointedContraction).toFun
      (UModel (overlapToPiece (X := W) (U := U) (V := V) true overlapBase)) =
    ((1, 1) : Torus)
  rw [show UModel
      (overlapToPiece (X := W) (U := U) (V := V) true overlapBase) =
        quotientMap ((1, 1) : Torus) puncturedCircleBase (.inl (1, 1)) by
    convert UModel_left ((1, 1) : Torus) using 1]
  rfl

theorem right_coordinate_map_strict :
    VHomotopyEquiv.toFun.comp
      ((overlapToPiece (X := W) (U := U) (V := V) false).comp
        UVHomotopyEquiv.invFun) = rightConst := by
  apply ContinuousMap.ext
  intro u
  cases u
  change VHomotopyEquiv.toFun
      (overlapToPiece (X := W) (U := U) (V := V) false
        (UVHomotopyEquiv.invFun ())) = (1 : Circle)
  rw [UVHomotopyEquiv_invFun_unit]
  change (wedgeHomotopyEquivLeft puncturedTorusPointedContraction).toFun
      (wedgeSwap
        (VModel (overlapToPiece (X := W) (U := U) (V := V) false overlapBase))) =
    (1 : Circle)
  rw [show VModel
      (overlapToPiece (X := W) (U := U) (V := V) false overlapBase) =
        quotientMap (puncturedCircleBase, puncturedCircleBase) (1 : Circle)
          (.inl (puncturedCircleBase, puncturedCircleBase)) by
    convert VModel_left ((1, 1) : Torus) one_one_mem_N using 1]
  rfl

def leftCoordinateHomotopy : ContinuousMap.Homotopy
    (UHomotopyEquiv.toFun.comp
      ((overlapToPiece (X := W) (U := U) (V := V) true).comp
        UVHomotopyEquiv.invFun)) leftConst := by
  rw [left_coordinate_map_strict]
  exact ContinuousMap.Homotopy.refl leftConst

def rightCoordinateHomotopy : ContinuousMap.Homotopy
    (VHomotopyEquiv.toFun.comp
      ((overlapToPiece (X := W) (U := U) (V := V) false).comp
        UVHomotopyEquiv.invFun)) rightConst := by
  rw [right_coordinate_map_strict]
  exact ContinuousMap.Homotopy.refl rightConst

def eK : FundamentalGroupoid UV ≌ FundamentalGroupoid Unit :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv UVHomotopyEquiv

def eL : FundamentalGroupoid U ≌ FundamentalGroupoid Torus :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv UHomotopyEquiv

def eR : FundamentalGroupoid V ≌ FundamentalGroupoid Circle :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv VHomotopyEquiv

def αL : eK.inverse ⋙ actualLeft ⋙ eL.functor ≅ coordinateLeft := by
  change FundamentalGroupoid.map UVHomotopyEquiv.invFun ⋙
      FundamentalGroupoid.map
        (overlapToPiece (X := W) (U := U) (V := V) true) ⋙
      FundamentalGroupoid.map UHomotopyEquiv.toFun ≅
    FundamentalGroupoid.map leftConst
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp]
  exact asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso
    leftCoordinateHomotopy)

def αR : eK.inverse ⋙ actualRight ⋙ eR.functor ≅ coordinateRight := by
  change FundamentalGroupoid.map UVHomotopyEquiv.invFun ⋙
      FundamentalGroupoid.map
        (overlapToPiece (X := W) (U := U) (V := V) false) ⋙
      FundamentalGroupoid.map VHomotopyEquiv.toFun ≅
    FundamentalGroupoid.map rightConst
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp]
  exact asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso
    rightCoordinateHomotopy)

def coordinatePseudoCoconeEquivalence {C : Type*} [Category C] :
    SpanPseudoCocone actualLeft actualRight C ≌
      SpanPseudoCocone coordinateLeft coordinateRight C :=
  pseudoCoconeEquivalenceOfSpanEquivalences
    actualLeft actualRight coordinateLeft coordinateRight eK eL eR αL αR

def coordinatePseudoCoconePostcomposeIso
    {C D : Type*} [Category C] [Category D] (H : Functor C D) :
    postcomposeFunctor H ⋙ (coordinatePseudoCoconeEquivalence (C := D)).functor ≅
      (coordinatePseudoCoconeEquivalence (C := C)).functor ⋙
        postcomposeFunctor H :=
  equivalenceFunctorPostcomposeIso
    actualLeft actualRight coordinateLeft coordinateRight eK eL eR αL αR H

theorem eK_inverse_unit_obj :
    eK.inverse.obj ⟨()⟩ = ⟨overlapBase⟩ := by
  apply FundamentalGroupoid.ext
  exact UVHomotopyEquiv_invFun_unit

theorem left_leg_base_obj :
    eL.functor.obj (actualLeft.obj (eK.inverse.obj ⟨()⟩)) =
      ⟨((1, 1) : Torus)⟩ := by
  apply FundamentalGroupoid.ext
  rw [eK_inverse_unit_obj]
  exact congrArg (fun f : C(Unit, Torus) => f ()) left_coordinate_map_strict

theorem right_leg_base_obj :
    eR.functor.obj (actualRight.obj (eK.inverse.obj ⟨()⟩)) =
      ⟨(1 : Circle)⟩ := by
  apply FundamentalGroupoid.ext
  rw [eK_inverse_unit_obj]
  exact congrArg (fun f : C(Unit, Circle) => f ()) right_coordinate_map_strict

#print axioms leftCoordinateHomotopy
#print axioms rightCoordinateHomotopy
#print axioms αL
#print axioms αR
#print axioms coordinatePseudoCoconeEquivalence
#print axioms coordinatePseudoCoconePostcomposeIso

end ConstructionTargets.TorusCircleWedgeFundamentalGroupoidSpan
