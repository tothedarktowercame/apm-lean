import ConstructionTargets.TorusCircleWedgeFundamentalGroupoidSpan
import ConstructionTargets.ConnectedGroupoidSingleObjEquivalence
import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.CircleHomology

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TorusCircleWedgeConnectorComparison

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.ConnectedGroupoidSingleObjEquivalence
open ConstructionTargets.TorusCircleWedgeFundamentalGroupoidSpan
open ConstructionTargets.FundamentalGroupProduct
open ConstructionTargets.CircleUniversalCover
local instance circlePathConnectedSpace : PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have hc : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using hc)

local instance torusPathConnectedSpace : PathConnectedSpace (Circle × Circle) :=
  ⟨⟨(1, 1)⟩, fun x y =>
    ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1)
      (PathConnectedSpace.somePath x.2 y.2)⟩⟩

def basedConnector {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (x₀ : X) (Y : FundamentalGroupoid X) : FundamentalGroupoid.mk x₀ ≅ Y := by
  classical
  if h : Y = FundamentalGroupoid.mk x₀ then
    exact eqToIso h.symm
  else
    exact asIso (Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath x₀ Y.as))

@[simp] theorem basedConnector_base {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x₀ : X) :
    basedConnector x₀ (FundamentalGroupoid.mk x₀) = Iso.refl _ := by
  classical
  simp [basedConnector]

def unitConnectors : ConnectorSystem (FundamentalGroupoid Unit) where
  base := FundamentalGroupoid.mk ()
  connector := basedConnector ()

def torusConnectors : ConnectorSystem (FundamentalGroupoid (Circle × Circle)) where
  base := FundamentalGroupoid.mk ((1, 1) : Circle × Circle)
  connector := basedConnector (1, 1)

def circleConnectors : ConnectorSystem (FundamentalGroupoid Circle) where
  base := FundamentalGroupoid.mk (1 : Circle)
  connector := basedConnector 1

@[simp] theorem unitConnectors_base_connector :
    unitConnectors.connector unitConnectors.base = Iso.refl _ :=
  basedConnector_base ()

@[simp] theorem torusConnectors_base_connector :
    torusConnectors.connector torusConnectors.base = Iso.refl _ :=
  basedConnector_base (1, 1)

@[simp] theorem circleConnectors_base_connector :
    circleConnectors.connector circleConnectors.base = Iso.refl _ :=
  basedConnector_base 1

theorem coordinateLeft_base :
    coordinateLeft.obj unitConnectors.base = torusConnectors.base := rfl

theorem coordinateRight_base :
    coordinateRight.obj unitConnectors.base = circleConnectors.base := rfl

theorem coordinateLeft_connector (X : FundamentalGroupoid Unit) :
    coordinateLeft.mapIso (unitConnectors.connector X) =
      (eqToIso (rfl : coordinateLeft.obj unitConnectors.base =
        torusConnectors.base)).trans
        (torusConnectors.connector (coordinateLeft.obj X)) := by
  apply Iso.ext
  cases X with
  | mk x =>
      cases x
      rw [show unitConnectors.connector (FundamentalGroupoid.mk ()) = Iso.refl _ by
        exact unitConnectors_base_connector]
      rw [Functor.mapIso_refl]
      rw [show torusConnectors.connector
          (coordinateLeft.obj (FundamentalGroupoid.mk ())) = Iso.refl _ by
        exact torusConnectors_base_connector]
      simp
      change 𝟙 torusConnectors.base = 𝟙 torusConnectors.base
      rfl

theorem coordinateRight_connector (X : FundamentalGroupoid Unit) :
    coordinateRight.mapIso (unitConnectors.connector X) =
      (eqToIso (rfl : coordinateRight.obj unitConnectors.base =
        circleConnectors.base)).trans
        (circleConnectors.connector (coordinateRight.obj X)) := by
  apply Iso.ext
  cases X with
  | mk x =>
      cases x
      rw [show unitConnectors.connector (FundamentalGroupoid.mk ()) = Iso.refl _ by
        exact unitConnectors_base_connector]
      rw [Functor.mapIso_refl]
      rw [show circleConnectors.connector
          (coordinateRight.obj (FundamentalGroupoid.mk ())) = Iso.refl _ by
        exact circleConnectors_base_connector]
      simp
      change 𝟙 circleConnectors.base = 𝟙 circleConnectors.base
      rfl

def coordinateLeftConnectorComparison :
    (connectorSingleObjEquivalence unitConnectors).inverse ⋙ coordinateLeft ⋙
        (connectorSingleObjEquivalence torusConnectors).functor ≅
      (inducedVertexHom coordinateLeft unitConnectors torusConnectors
        rfl).toFunctor :=
  connectorFunctorComparison coordinateLeft unitConnectors torusConnectors
    rfl coordinateLeft_connector

def coordinateRightConnectorComparison :
    (connectorSingleObjEquivalence unitConnectors).inverse ⋙ coordinateRight ⋙
        (connectorSingleObjEquivalence circleConnectors).functor ≅
      (inducedVertexHom coordinateRight unitConnectors circleConnectors
        rfl).toFunctor :=
  connectorFunctorComparison coordinateRight unitConnectors circleConnectors
    rfl coordinateRight_connector

def unitEndMulEquiv : End unitConnectors.base ≃* PUnit :=
  { toFun := fun _ => ()
    invFun := fun _ => Path.Homotopic.Quotient.mk (Path.refl ())
    left_inv := fun x => by
      change Path.Homotopic.Quotient.mk (Path.refl ()) = x
      exact @Subsingleton.elim (Path.Homotopic.Quotient () ()) inferInstance _ _
    right_inv := fun x => by cases x; rfl
    map_mul' := fun _ _ => rfl }

def torusEndMulEquiv : End torusConnectors.base ≃* Multiplicative (ℤ × ℤ) :=
  (fundamentalGroupProdMulEquiv (1 : Circle) (1 : Circle)).trans
    ((circleFundamentalGroupMulEquivInt.prodCongr
      circleFundamentalGroupMulEquivInt).trans
        (MulEquiv.prodMultiplicative ℤ ℤ).symm)

def circleEndMulEquiv : End circleConnectors.base ≃* Multiplicative ℤ :=
  circleFundamentalGroupMulEquivInt

def unitCoordinateEquivalence :
    FundamentalGroupoid Unit ≌ SingleObj PUnit :=
  (connectorSingleObjEquivalence unitConnectors).trans unitEndMulEquiv.toSingleObjEquiv

def torusCoordinateEquivalence :
    FundamentalGroupoid (Circle × Circle) ≌ SingleObj (Multiplicative (ℤ × ℤ)) :=
  (connectorSingleObjEquivalence torusConnectors).trans torusEndMulEquiv.toSingleObjEquiv

def circleCoordinateEquivalence :
    FundamentalGroupoid Circle ≌ SingleObj (Multiplicative ℤ) :=
  (connectorSingleObjEquivalence circleConnectors).trans circleEndMulEquiv.toSingleObjEquiv

#print axioms coordinateLeftConnectorComparison
#print axioms coordinateRightConnectorComparison
#print axioms unitCoordinateEquivalence
#print axioms torusCoordinateEquivalence
#print axioms circleCoordinateEquivalence

end ConstructionTargets.TorusCircleWedgeConnectorComparison
