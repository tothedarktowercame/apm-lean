import ConstructionTargets.TwiceSpiralConnectorLegCompatibility
import ConstructionTargets.TwiceSpiralH1Coordinates

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralConnectorExistence

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorVertexData
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

universe u v u' v'

variable {G : Type u} [Groupoid.{v} G]
variable {H : Type u'} [Groupoid.{v'} H]

private theorem mapIso_trans_eq (F : Functor G H) (S : ConnectorSystem G)
    (X' X : G) (e : F.obj X' = F.obj X) (hx : X' = X) :
    (F.mapIso (S.connector X')).trans (eqToIso e) =
      F.mapIso (S.connector X) := by
  subst X'
  simp

/-- Extend prescribed connectors along a functor injective on objects.
The target base is definitionally the image of the source base. -/
def extendConnector (F : Functor G H) (_hF : Function.Injective F.obj)
    (S : ConnectorSystem G) (fallback : ∀ Y : H, F.obj S.base ≅ Y) :
    ∀ Y : H, F.obj S.base ≅ Y := by
  classical
  exact fun Y ↦
    if h : ∃ X : G, F.obj X = Y then
      (F.mapIso (S.connector h.choose)).trans (eqToIso h.choose_spec)
    else fallback Y

theorem extendConnector_apply (F : Functor G H) (hF : Function.Injective F.obj)
    (S : ConnectorSystem G) (fallback : ∀ Y : H, F.obj S.base ≅ Y) (X : G) :
    extendConnector F hF S fallback (F.obj X) = F.mapIso (S.connector X) := by
  classical
  rw [extendConnector, dif_pos ⟨X, rfl⟩]
  let h : ∃ X' : G, F.obj X' = F.obj X := ⟨X, rfl⟩
  have hx : h.choose = X := hF h.choose_spec
  exact mapIso_trans_eq F S h.choose X h.choose_spec hx

def extendConnectorSystem (F : Functor G H) (hF : Function.Injective F.obj)
    (S : ConnectorSystem G) (fallback : ∀ Y : H, F.obj S.base ≅ Y) :
    ConnectorSystem H := ⟨F.obj S.base, extendConnector F hF S fallback⟩

theorem extendConnectorSystem_connector_apply
    (F : Functor G H) (hF : Function.Injective F.obj)
    (S : ConnectorSystem G) (fallback : ∀ Y : H, F.obj S.base ≅ Y) (X : G) :
    (extendConnectorSystem F hF S fallback).connector (F.obj X) =
      F.mapIso (S.connector X) :=
  extendConnector_apply F hF S fallback X

theorem boundaryInclusion_injective : Function.Injective boundaryInclusion := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : SolidTorus ↦ z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : SolidTorus ↦ z.2.1) hxy

theorem coordinateLeftLeg_obj_injective :
    Function.Injective coordinateLeftLeg.obj := by
  intro X Y hXY
  apply FundamentalGroupoid.ext
  apply boundaryInclusion_injective
  exact congrArg FundamentalGroupoid.as hXY

theorem coordinateRightLeg_obj_injective
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Function.Injective (coordinateRightLeg h).obj := by
  intro X Y hXY
  apply FundamentalGroupoid.ext
  apply h.injective
  apply boundaryInclusion_injective
  exact congrArg FundamentalGroupoid.as hXY

local instance circlePathConnectedSpace : PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have hc : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using hc)

local instance solidTorusPathConnectedSpace : PathConnectedSpace SolidTorus :=
  ⟨⟨(1, 0)⟩, fun x y ↦ by
    let hjoined := (convex_closedBall (0 : Plane) 1).isPathConnected (by simp) |>.joinedIn
      x.2.1 x.2.2 y.2.1 y.2.2
    let γ := hjoined.choose
    let γD : Path x.2 y.2 :=
      { toFun := fun t ↦ ⟨γ t, hjoined.choose_spec t⟩
        continuous_toFun := γ.continuous.subtype_mk _
        source' := Subtype.ext γ.source
        target' := Subtype.ext γ.target }
    exact ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1) γD⟩⟩

local instance boundaryTorusPathConnectedSpace : PathConnectedSpace BoundaryTorus :=
  ConstructionTargets.BoundaryTorusHurewiczIsomorphism.boundaryTorusPathConnectedSpace

def fundamentalConnector {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (x₀ : X) (y : FundamentalGroupoid X) : FundamentalGroupoid.mk x₀ ≅ y :=
  asIso (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ y.as))

theorem nonempty_legCompatibleConnectorSystems
    {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
    (B : PointedCoordinateBases h d) : Nonempty (LegCompatibleConnectorSystems B) := by
  let boundary : ConnectorSystem (FundamentalGroupoid BoundaryTorus) :=
    { base := FundamentalGroupoid.mk B.boundaryBase
      connector := fundamentalConnector B.boundaryBase }
  let left := extendConnectorSystem coordinateLeftLeg coordinateLeftLeg_obj_injective
    boundary (fundamentalConnector B.leftBase)
  let right := extendConnectorSystem (coordinateRightLeg h)
    (coordinateRightLeg_obj_injective h) boundary (fundamentalConnector B.rightBase)
  let coordinate : CoordinateConnectorSystems B :=
    { boundaryConnector := boundary.connector
      leftConnector := left.connector
      rightConnector := right.connector }
  refine ⟨⟨coordinate, ?_, ?_⟩⟩
  · intro X
    simpa [coordinate, left] using
      (extendConnectorSystem_connector_apply coordinateLeftLeg
        coordinateLeftLeg_obj_injective boundary (fundamentalConnector B.leftBase) X).symm
  · intro X
    simpa [coordinate, right] using
      (extendConnectorSystem_connector_apply (coordinateRightLeg h)
        (coordinateRightLeg_obj_injective h) boundary
        (fundamentalConnector B.rightBase) X).symm

/-- An existing based coordinate interface supplies compatible connectors without
any additional premise. -/
example {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
    (coordinates : BasedTwiceSpiralCoordinateInterface h d) :
    Nonempty (LegCompatibleConnectorSystems
      ({ coordinates := coordinates } : PointedCoordinateBases h d)) :=
  nonempty_legCompatibleConnectorSystems { coordinates := coordinates }

end ConstructionTargets.TwiceSpiralConnectorExistence
