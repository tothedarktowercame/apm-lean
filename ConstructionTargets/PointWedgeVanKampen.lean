import ConstructionTargets.ThreeCirclesPathTopology
import ConstructionTargets.GenericTargetNaturalSourceReconstruction
import ConstructionTargets.PointedPuncturedCircleContraction
import ConstructionTargets.PointWedgeRestrictedOpenQuotient
import ConstructionTargets.GenericPointWedgeOverlapInclusionSquares
import ConstructionTargets.GenericSpanPseudoCoconeTransport
import ConstructionTargets.TwoOpenFundamentalGroupoidSpan
import ConstructionTargets.ConnectedGroupoidSingleObjEquivalence
import ConstructionTargets.FreeProductPointSpanRepresentations
import ConstructionTargets.TwoOpenFreeProductMapping
import ConstructionTargets.FreeProductRepresentationSingleObjEquivalence
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
open PointWedgePointedContractionDescent
open PointWedgeQuotient PointWedgeRestrictedOpenQuotient
open GenericPointWedgeOpenCoverComparison
open GenericPointWedgeOverlapInclusionSquares
open GenericSpanPseudoCoconeTransport
open TwoOpenFundamentalGroupoidSpan
open ConnectedGroupoidVertexReconstruction
open ConnectedGroupoidSingleObjEquivalence
open FreeProductPointSpanRepresentations
open TwoOpenFundamentalGroupoidPseudopushout
open FreeProductRepresentationSingleObjEquivalence

universe u

section GenericMappingCoordinates

variable {X : Type} {Y : Type}
variable [TopologicalSpace X] [TopologicalSpace Y]

abbrev genericPointWedgeLeftPiece (x₀ : X) (y₀ : Y) (M : Set Y) :=
  {z // z ∈ leftOpen x₀ y₀ M}

abbrev genericPointWedgeRightPiece (x₀ : X) (y₀ : Y) (N : Set X) :=
  {z // z ∈ rightOpen x₀ y₀ N}

abbrev genericPointWedgeOverlapPiece
    (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X) :=
  {z // z ∈ leftOpen x₀ y₀ M ∩ rightOpen x₀ y₀ N}

def genericPointWedgeActualLeft
    (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X) :
    FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) ⥤
      FundamentalGroupoid (genericPointWedgeLeftPiece x₀ y₀ M) :=
  FundamentalGroupoid.map (overlapToLeft x₀ y₀ M N)

def genericPointWedgeActualRight
    (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X) :
    FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) ⥤
      FundamentalGroupoid (genericPointWedgeRightPiece x₀ y₀ N) :=
  FundamentalGroupoid.map (overlapToRight x₀ y₀ M N)

def genericPointWedgeCoordinateLeft (x₀ : X) :
    FundamentalGroupoid Unit ⥤ FundamentalGroupoid X :=
  FundamentalGroupoid.map (ContinuousMap.const Unit x₀)

def genericPointWedgeCoordinateRight (y₀ : Y) :
    FundamentalGroupoid Unit ⥤ FundamentalGroupoid Y :=
  FundamentalGroupoid.map (ContinuousMap.const Unit y₀)

variable (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
variable (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
variable (cM : PointedContraction M ⟨y₀, hy⟩)
variable (cN : PointedContraction N ⟨x₀, hx⟩)

private abbrev genericPointWedgePackage :=
  genericPointWedgeCoverPackage x₀ y₀ M N hM hN hy hx cM cN

def genericPointWedgeOverlapGroupoidEquivalence :
    FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) ≌
      FundamentalGroupoid Unit :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).intersectionEquiv

def genericPointWedgeLeftGroupoidEquivalence :
    FundamentalGroupoid (genericPointWedgeLeftPiece x₀ y₀ M) ≌
      FundamentalGroupoid X :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftEquiv

def genericPointWedgeRightGroupoidEquivalence :
    FundamentalGroupoid (genericPointWedgeRightPiece x₀ y₀ N) ≌
      FundamentalGroupoid Y :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightEquiv

def genericPointWedgeLeftSpanIso :
    (genericPointWedgeOverlapGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN).inverse ⋙
        genericPointWedgeActualLeft x₀ y₀ M N ⋙
        (genericPointWedgeLeftGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN).functor ≅
      genericPointWedgeCoordinateLeft x₀ := by
  change FundamentalGroupoid.map
        (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).intersectionEquiv.invFun ⋙
      FundamentalGroupoid.map (overlapToLeft x₀ y₀ M N) ⋙
      FundamentalGroupoid.map
        (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun ≅
      FundamentalGroupoid.map (ContinuousMap.const Unit x₀)
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp]
  have h := (genericPointWedgeOverlapInclusionSquares
    x₀ y₀ M N hM hN hy hx cM cN).1
  have h' :
      ((genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun.comp
        (overlapToLeft x₀ y₀ M N)).comp
          (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).intersectionEquiv.invFun =
        ContinuousMap.const Unit x₀ := by
    simpa only [ContinuousMap.comp_assoc] using h
  rw [h']

def genericPointWedgeRightSpanIso :
    (genericPointWedgeOverlapGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN).inverse ⋙
        genericPointWedgeActualRight x₀ y₀ M N ⋙
        (genericPointWedgeRightGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN).functor ≅
      genericPointWedgeCoordinateRight y₀ := by
  change FundamentalGroupoid.map
        (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).intersectionEquiv.invFun ⋙
      FundamentalGroupoid.map (overlapToRight x₀ y₀ M N) ⋙
      FundamentalGroupoid.map
        (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun ≅
      FundamentalGroupoid.map (ContinuousMap.const Unit y₀)
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp]
  have h := (genericPointWedgeOverlapInclusionSquares
    x₀ y₀ M N hM hN hy hx cM cN).2
  have h' :
      ((genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun.comp
        (overlapToRight x₀ y₀ M N)).comp
          (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).intersectionEquiv.invFun =
        ContinuousMap.const Unit y₀ := by
    simpa only [ContinuousMap.comp_assoc] using h
  rw [h']

def genericPointWedgeCoordinateSpanEquivalence
    (C : Type u) [Category C] :
    SpanPseudoCocone
        (genericPointWedgeActualLeft x₀ y₀ M N)
        (genericPointWedgeActualRight x₀ y₀ M N) C ≌
      SpanPseudoCocone
        (genericPointWedgeCoordinateLeft x₀)
        (genericPointWedgeCoordinateRight y₀) C :=
  pseudoCoconeEquivalenceOfSpanEquivalences
    (genericPointWedgeActualLeft x₀ y₀ M N)
    (genericPointWedgeActualRight x₀ y₀ M N)
    (genericPointWedgeCoordinateLeft x₀)
    (genericPointWedgeCoordinateRight y₀)
    (genericPointWedgeOverlapGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeLeftGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeRightGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeLeftSpanIso x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeRightSpanIso x₀ y₀ M N hM hN hy hx cM cN)

def genericPointWedgeCoordinateSpanPostcomposeIso
    {C D : Type u} [Category C] [Category D] (K : C ⥤ D) :
    postcomposeFunctor K ⋙
        (genericPointWedgeCoordinateSpanEquivalence
          x₀ y₀ M N hM hN hy hx cM cN D).functor ≅
      (genericPointWedgeCoordinateSpanEquivalence
          x₀ y₀ M N hM hN hy hx cM cN C).functor ⋙
        postcomposeFunctor K :=
  equivalenceFunctorPostcomposeIso
    (genericPointWedgeActualLeft x₀ y₀ M N)
    (genericPointWedgeActualRight x₀ y₀ M N)
    (genericPointWedgeCoordinateLeft x₀)
    (genericPointWedgeCoordinateRight y₀)
    (genericPointWedgeOverlapGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeLeftGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeRightGroupoidEquivalence x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeLeftSpanIso x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeRightSpanIso x₀ y₀ M N hM hN hy hx cM cN) K

end GenericMappingCoordinates

section GenericPointSpanCoordinates

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [PathConnectedSpace X] [PathConnectedSpace Y]

def genericPointWedgeBasedConnector
    {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z]
    (z₀ : Z) (A : FundamentalGroupoid Z) : FundamentalGroupoid.mk z₀ ≅ A := by
  classical
  if h : A = FundamentalGroupoid.mk z₀ then
    exact eqToIso h.symm
  else
    exact asIso (Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath z₀ A.as))

@[simp] theorem genericPointWedgeBasedConnector_base
    {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z₀ : Z) :
    genericPointWedgeBasedConnector z₀ (FundamentalGroupoid.mk z₀) =
      Iso.refl _ := by
  classical
  simp [genericPointWedgeBasedConnector]

def genericPointWedgeUnitConnectors :
    ConnectorSystem (FundamentalGroupoid Unit) where
  base := FundamentalGroupoid.mk ()
  connector := genericPointWedgeBasedConnector ()

def genericPointWedgeConnectors
    {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z₀ : Z) :
    ConnectorSystem (FundamentalGroupoid Z) where
  base := FundamentalGroupoid.mk z₀
  connector := genericPointWedgeBasedConnector z₀

def genericPointWedgeUnitEndMulEquiv :
    End genericPointWedgeUnitConnectors.base ≃* PUnit :=
  { toFun := fun _ => ()
    invFun := fun _ => Path.Homotopic.Quotient.mk (Path.refl ())
    left_inv := fun x => by
      change Path.Homotopic.Quotient.mk (Path.refl ()) = x
      exact @Subsingleton.elim (Path.Homotopic.Quotient () ()) inferInstance _ _
    right_inv := fun x => by cases x; rfl
    map_mul' := fun _ _ => rfl }

def genericPointWedgeUnitSingleObjEquivalence :
    FundamentalGroupoid Unit ≌ SingleObj PUnit :=
  (connectorSingleObjEquivalence genericPointWedgeUnitConnectors).trans
    genericPointWedgeUnitEndMulEquiv.toSingleObjEquiv

def genericPointWedgeSingleObjEquivalence
    {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z₀ : Z) :
    FundamentalGroupoid Z ≌ SingleObj (FundamentalGroup Z z₀) :=
  connectorSingleObjEquivalence (genericPointWedgeConnectors z₀)

/-- Every functor out of the trivial one-object group is naturally isomorphic
to the point leg.  This comparison avoids choosing a normalization for an
arbitrary equivalence's counit. -/
def genericPointWedgeTrivialSourceFunctorIso
    (G : Type) [Monoid G] (F : SingleObj PUnit ⥤ SingleObj G) :
    F ≅ pointLeg G :=
  NatIso.ofComponents
    (fun A => eqToIso (Subsingleton.elim (F.obj A) ((pointLeg G).obj A))) (by
      intro A B f
      cases A
      cases B
      rw [show f = (𝟙 (SingleObj.star PUnit) :
          (SingleObj.star PUnit) ⟶ (SingleObj.star PUnit)) by
        change (f : PUnit) = PUnit.unit
        let p : PUnit := f
        change p = PUnit.unit
        cases p
        rfl]
      have hF : F.map (𝟙 (SingleObj.star PUnit)) = 𝟙 _ := F.map_id _
      have hP : (pointLeg G).map (𝟙 (SingleObj.star PUnit)) = 𝟙 _ :=
        (pointLeg G).map_id _
      erw [hF, hP]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)

variable (x₀ : X) (y₀ : Y)

def genericPointWedgeCoordinateLeftPointIso :
    genericPointWedgeUnitSingleObjEquivalence.inverse ⋙
        genericPointWedgeCoordinateLeft x₀ ⋙
        (genericPointWedgeSingleObjEquivalence x₀).functor ≅
      pointLeg (FundamentalGroup X x₀) :=
  genericPointWedgeTrivialSourceFunctorIso _ _

def genericPointWedgeCoordinateRightPointIso :
    genericPointWedgeUnitSingleObjEquivalence.inverse ⋙
        genericPointWedgeCoordinateRight y₀ ⋙
        (genericPointWedgeSingleObjEquivalence y₀).functor ≅
      pointLeg (FundamentalGroup Y y₀) :=
  genericPointWedgeTrivialSourceFunctorIso _ _

def genericPointWedgeCoordinatePointSpanEquivalence
    (C : Type u) [Category C] :
    SpanPseudoCocone
        (genericPointWedgeCoordinateLeft x₀)
        (genericPointWedgeCoordinateRight y₀) C ≌
      SpanPseudoCocone
        (pointLeg (FundamentalGroup X x₀))
        (pointLeg (FundamentalGroup Y y₀)) C :=
  pseudoCoconeEquivalenceOfSpanEquivalences
    (genericPointWedgeCoordinateLeft x₀)
    (genericPointWedgeCoordinateRight y₀)
    (pointLeg (FundamentalGroup X x₀))
    (pointLeg (FundamentalGroup Y y₀))
    genericPointWedgeUnitSingleObjEquivalence
    (genericPointWedgeSingleObjEquivalence x₀)
    (genericPointWedgeSingleObjEquivalence y₀)
    (genericPointWedgeCoordinateLeftPointIso x₀)
    (genericPointWedgeCoordinateRightPointIso y₀)

def genericPointWedgeCoordinatePointSpanPostcomposeIso
    {C D : Type u} [Category C] [Category D] (K : C ⥤ D) :
    postcomposeFunctor K ⋙
        (genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ D).functor ≅
      (genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C).functor ⋙
        postcomposeFunctor K :=
  equivalenceFunctorPostcomposeIso
    (genericPointWedgeCoordinateLeft x₀)
    (genericPointWedgeCoordinateRight y₀)
    (pointLeg (FundamentalGroup X x₀))
    (pointLeg (FundamentalGroup Y y₀))
    genericPointWedgeUnitSingleObjEquivalence
    (genericPointWedgeSingleObjEquivalence x₀)
    (genericPointWedgeSingleObjEquivalence y₀)
    (genericPointWedgeCoordinateLeftPointIso x₀)
    (genericPointWedgeCoordinateRightPointIso y₀) K

end GenericPointSpanCoordinates

section GenericSingleObjMapping

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [PathConnectedSpace X] [PathConnectedSpace Y]
variable (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
variable (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
variable (cM : PointedContraction M ⟨y₀, hy⟩)
variable (cN : PointedContraction N ⟨x₀, hx⟩)

private abbrev genericLeftOpen := leftOpen x₀ y₀ M
private abbrev genericRightOpen := rightOpen x₀ y₀ N

def genericPointWedgePseudoSpanEquivalence (C : Type) [Category C] :
    PseudoFunctorCocone (X := Wedge x₀ y₀)
        (U := genericLeftOpen x₀ y₀ M)
        (V := genericRightOpen x₀ y₀ N) (C := C) ≌
      SpanPseudoCocone
        (genericPointWedgeActualLeft x₀ y₀ M N)
        (genericPointWedgeActualRight x₀ y₀ M N) C :=
  ConstructionTargets.TwoOpenFreeProductMapping.pseudoSpanEquivalence C

abbrev genericPointWedgeLeftGroup := FundamentalGroup X x₀
abbrev genericPointWedgeRightGroup := FundamentalGroup Y y₀
abbrev genericPointWedgeFreeProduct :=
  Monoid.Coprod (genericPointWedgeLeftGroup x₀)
    (genericPointWedgeRightGroup y₀)

/-- The B3 mapping equivalence before transporting the actual cover span to
the fixed coordinate span. -/
def genericPointWedgePreCoordinateSpanMappingEquivalence
    (C : Type) [Category C] :
    (FundamentalGroupoid (Wedge x₀ y₀) ⥤ C) ≌
      SpanPseudoCocone
        (genericPointWedgeActualLeft x₀ y₀ M N)
        (genericPointWedgeActualRight x₀ y₀ M N) C :=
  (twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C)
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ).trans
    (genericPointWedgePseudoSpanEquivalence x₀ y₀ M N C)

/-- The B3 mapping equivalence before the final point-span representation is
converted into a free-product representation. -/
def genericPointWedgePreCoordinatePointSpanMappingEquivalence
    (C : Type) [Category C] :
    (FundamentalGroupoid (Wedge x₀ y₀) ⥤ C) ≌
      SpanPseudoCocone
        (genericPointWedgeCoordinateLeft x₀)
        (genericPointWedgeCoordinateRight y₀) C :=
  ((twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C)
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ).trans
    (genericPointWedgePseudoSpanEquivalence x₀ y₀ M N C)).trans
    (genericPointWedgeCoordinateSpanEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C)

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
theorem genericPointWedgePreCoordinatePointSpanMappingEquivalence_eq_preCoordinateSpan_trans
    (C : Type) [Category C] :
    genericPointWedgePreCoordinatePointSpanMappingEquivalence
        x₀ y₀ M N hM hN hy hx cM cN C =
      (genericPointWedgePreCoordinateSpanMappingEquivalence
        x₀ y₀ M N hM hN hy hx cM cN C).trans
          (genericPointWedgeCoordinateSpanEquivalence
            x₀ y₀ M N hM hN hy hx cM cN C) := by
  rfl

def genericPointWedgePreFreeProductMappingEquivalence
    (C : Type) [Category C] :
    (FundamentalGroupoid (Wedge x₀ y₀) ⥤ C) ≌
      SpanPseudoCocone
        (pointLeg (genericPointWedgeLeftGroup x₀))
        (pointLeg (genericPointWedgeRightGroup y₀)) C :=
  (((twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C)
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ).trans
    (genericPointWedgePseudoSpanEquivalence x₀ y₀ M N C)).trans
    (genericPointWedgeCoordinateSpanEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C)).trans
    (genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C)

theorem genericPointWedgePreFreeProductMappingEquivalence_eq_preCoordinate_trans
    (C : Type) [Category C] :
    genericPointWedgePreFreeProductMappingEquivalence
        x₀ y₀ M N hM hN hy hx cM cN C =
      (genericPointWedgePreCoordinatePointSpanMappingEquivalence
        x₀ y₀ M N hM hN hy hx cM cN C).trans
          (genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C) := by
  rfl

def genericPointWedgeFreeProductMappingEquivalence
    (C : Type) [Category C] :
    (FundamentalGroupoid (Wedge x₀ y₀) ⥤ C) ≌
      FreeProductRepresentation (C := C)
        (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) :=
  ((((twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C)
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ).trans
    (genericPointWedgePseudoSpanEquivalence x₀ y₀ M N C)).trans
    (genericPointWedgeCoordinateSpanEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C)).trans
    (genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C)).trans
    (freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C)

theorem genericPointWedgeFreeProductMappingEquivalence_eq_pre_trans
    (C : Type) [Category C] :
    genericPointWedgeFreeProductMappingEquivalence
        x₀ y₀ M N hM hN hy hx cM cN C =
      (genericPointWedgePreFreeProductMappingEquivalence
        x₀ y₀ M N hM hN hy hx cM cN C).trans
          (freeProductPointSpanEquivalence
            (genericPointWedgeLeftGroup x₀)
            (genericPointWedgeRightGroup y₀) C) := by
  rfl

def genericPointWedgeSingleObjMappingEquivalence
    (C : Type) [Category C] :
    (FundamentalGroupoid (Wedge x₀ y₀) ⥤ C) ≌
      (SingleObj (genericPointWedgeFreeProduct x₀ y₀) ⥤ C) :=
  (genericPointWedgeFreeProductMappingEquivalence
    x₀ y₀ M N hM hN hy hx cM cN C).trans
      (representationSingleObjEquivalence
        (C := C) (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀))

/-- The first object encountered when evaluating the inverse of the full B3
equivalence at the identity functor. -/
def genericPointWedgeIdentityRepresentation :
    FreeProductRepresentation
      (C := SingleObj (genericPointWedgeFreeProduct x₀ y₀))
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) :=
  (representationSingleObjEquivalence
    (C := SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    (genericPointWedgeLeftGroup x₀)
    (genericPointWedgeRightGroup y₀)).inverse.obj
      (𝟭 (SingleObj (genericPointWedgeFreeProduct x₀ y₀)))

/-- The next inverse stage of B3, obtained by restricting the identity
representation to the two point-span legs. -/
def genericPointWedgeIdentityPointSpan :
    SpanPseudoCocone
      (pointLeg (genericPointWedgeLeftGroup x₀))
      (pointLeg (genericPointWedgeRightGroup y₀))
      (SingleObj (genericPointWedgeFreeProduct x₀ y₀)) :=
  (freeProductPointSpanEquivalence
    (genericPointWedgeLeftGroup x₀)
    (genericPointWedgeRightGroup y₀)
    (SingleObj (genericPointWedgeFreeProduct x₀ y₀))).inverse.obj
      (genericPointWedgeIdentityRepresentation x₀ y₀)

/-- The coordinate-span object one inverse stage earlier in B3. -/
def genericPointWedgeIdentityCoordinateSpan :
    SpanPseudoCocone
      (genericPointWedgeCoordinateLeft x₀)
      (genericPointWedgeCoordinateRight y₀)
      (SingleObj (genericPointWedgeFreeProduct x₀ y₀)) :=
  (genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀
    (SingleObj (genericPointWedgeFreeProduct x₀ y₀))).inverse.obj
      (genericPointWedgeIdentityPointSpan x₀ y₀)

/-- The B3 inverse object after transporting the coordinate span back across
the three homotopy equivalences of the literal cover span. -/
def genericPointWedgeIdentityActualSpan :
    SpanPseudoCocone
      (genericPointWedgeActualLeft x₀ y₀ M N)
      (genericPointWedgeActualRight x₀ y₀ M N)
      (SingleObj (genericPointWedgeFreeProduct x₀ y₀)) :=
  (genericPointWedgeCoordinateSpanEquivalence
    x₀ y₀ M N hM hN hy hx cM cN
    (SingleObj (genericPointWedgeFreeProduct x₀ y₀))).inverse.obj
      (genericPointWedgeIdentityCoordinateSpan x₀ y₀)

/-- The inverse coordinate transport underlying the actual-span object,
exposed before packaging it as the inverse of an equivalence. -/
def genericPointWedgeIdentityCoordinateReverseSpan :
    SpanPseudoCocone
      (genericPointWedgeActualLeft x₀ y₀ M N)
      (genericPointWedgeActualRight x₀ y₀ M N)
      (SingleObj (genericPointWedgeFreeProduct x₀ y₀)) :=
  reverseTransportObj
    (genericPointWedgeActualLeft x₀ y₀ M N)
    (genericPointWedgeActualRight x₀ y₀ M N)
    (genericPointWedgeCoordinateLeft x₀)
    (genericPointWedgeCoordinateRight y₀)
    (genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeLeftSpanIso x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeRightSpanIso x₀ y₀ M N hM hN hy hx cM cN)
    (genericPointWedgeIdentityCoordinateSpan x₀ y₀)

theorem genericPointWedgeIdentityActualSpan_eq_coordinateReverseSpan :
    genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN =
      genericPointWedgeIdentityCoordinateReverseSpan
        x₀ y₀ M N hM hN hy hx cM cN := rfl

theorem genericPointWedgeIdentityCoordinateReverseSpan_glue_app :
    let l := genericPointWedgeActualLeft x₀ y₀ M N
    let r := genericPointWedgeActualRight x₀ y₀ M N
    let l' := genericPointWedgeCoordinateLeft x₀
    let r' := genericPointWedgeCoordinateRight y₀
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eL := genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eR := genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aL := genericPointWedgeLeftSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let aR := genericPointWedgeRightSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (genericPointWedgeIdentityCoordinateReverseSpan
      x₀ y₀ M N hM hN hy hx cM cN).glue.hom.app z =
      (reverseLeftComparison l l' eK eL aL Q.left).inv.app z ≫
        (Functor.isoWhiskerLeft eK.functor Q.glue).hom.app z ≫
          (reverseRightComparison r r' eK eR aR Q.right).hom.app z := by
  rfl

/-- The inverse outer left comparison reverses its defining two factors at
the chosen overlap representative. -/
theorem genericPointWedgeIdentityOuterLeftComparison_app :
    let l := genericPointWedgeActualLeft x₀ y₀ M N
    let l' := genericPointWedgeCoordinateLeft x₀
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eL := genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aL := genericPointWedgeLeftSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (reverseLeftComparison l l' eK eL aL Q.left).inv.app z =
      (Functor.isoWhiskerRight
        (eK.funInvIdAssoc (l ⋙ eL.functor)) Q.left).inv.app z ≫
        (Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft eK.functor aL.symm) Q.left).inv.app z := by
  rfl

/-- The outer right comparison is its right-span factor followed by the
overlap-equivalence round-trip at the chosen overlap representative. -/
theorem genericPointWedgeIdentityOuterRightComparison_app :
    let r := genericPointWedgeActualRight x₀ y₀ M N
    let r' := genericPointWedgeCoordinateRight y₀
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eR := genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aR := genericPointWedgeRightSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (reverseRightComparison r r' eK eR aR Q.right).hom.app z =
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft eK.functor aR.symm) Q.right).hom.app z ≫
        (Functor.isoWhiskerRight
          (eK.funInvIdAssoc (r ⋙ eR.functor)) Q.right).hom.app z := by
  rfl

/-- The inverse left-span factor is the literal left-span comparison mapped
by the coordinate representation at the transported overlap object. -/
theorem genericPointWedgeIdentityOuterLeftSpanFactor_eq_map :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aL := genericPointWedgeLeftSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft eK.functor aL.symm) Q.left).inv.app z =
        Q.left.map (aL.hom.app (eK.functor.obj z)) := by
  rfl

/-- The right-span factor is the literal right-span comparison mapped by the
coordinate representation at the transported overlap object. -/
theorem genericPointWedgeIdentityOuterRightSpanFactor_eq_map :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aR := genericPointWedgeRightSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft eK.functor aR.symm) Q.right).hom.app z =
        Q.right.map (aR.inv.app (eK.functor.obj z)) := by
  rfl

/-- The inverse left overlap round-trip factor is the corresponding
equivalence component mapped by the coordinate representation. -/
theorem genericPointWedgeIdentityOuterLeftRoundTrip_eq_map :
    let l := genericPointWedgeActualLeft x₀ y₀ M N
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eL := genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (Functor.isoWhiskerRight
      (eK.funInvIdAssoc (l ⋙ eL.functor)) Q.left).inv.app z =
        Q.left.map ((eK.funInvIdAssoc (l ⋙ eL.functor)).inv.app z) := by
  rfl

/-- The forward right overlap round-trip factor is the corresponding
equivalence component mapped by the coordinate representation. -/
theorem genericPointWedgeIdentityOuterRightRoundTrip_eq_map :
    let r := genericPointWedgeActualRight x₀ y₀ M N
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eR := genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (Functor.isoWhiskerRight
      (eK.funInvIdAssoc (r ⋙ eR.functor)) Q.right).hom.app z =
        Q.right.map ((eK.funInvIdAssoc (r ⋙ eR.functor)).hom.app z) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The inverse left round-trip component is the left target functor applied
to the overlap equivalence's unit component. -/
theorem genericPointWedgeIdentityOuterLeftRoundTripComponent_eq_unitMap :
    let l := genericPointWedgeActualLeft x₀ y₀ M N
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eL := genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    ((eK.funInvIdAssoc (l ⋙ eL.functor)).inv.app z) =
      (l ⋙ eL.functor).map (eK.unit.app z) := by
  simp

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The forward right round-trip component is the right target functor applied
to the overlap equivalence's inverse unit component. -/
theorem genericPointWedgeIdentityOuterRightRoundTripComponent_eq_unitInvMap :
    let r := genericPointWedgeActualRight x₀ y₀ M N
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eR := genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    ((eK.funInvIdAssoc (r ⋙ eR.functor)).hom.app z) =
      (r ⋙ eR.functor).map (eK.unitInv.app z) := by
  simp

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The left target image of the overlap unit separates into the actual-left
map followed by the left equivalence functor map. -/
theorem genericPointWedgeIdentityOuterLeftUnit_targetMap_eq_nestedMap :
    let l := genericPointWedgeActualLeft x₀ y₀ M N
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eL := genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (l ⋙ eL.functor).map (eK.unit.app z) =
      eL.functor.map (l.map (eK.unit.app z)) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The right target image of the inverse overlap unit separates into the
actual-right map followed by the right equivalence functor map. -/
theorem genericPointWedgeIdentityOuterRightUnitInv_targetMap_eq_nestedMap :
    let r := genericPointWedgeActualRight x₀ y₀ M N
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eR := genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (r ⋙ eR.functor).map (eK.unitInv.app z) =
      eR.functor.map (r.map (eK.unitInv.app z)) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The inner left stage is literally the fundamental-groupoid map induced by
the overlap-to-left inclusion. -/
theorem genericPointWedgeIdentityOuterLeftUnit_actualMap_eq_inclusionMap :
    let l := genericPointWedgeActualLeft x₀ y₀ M N
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    l.map (eK.unit.app z) =
      (FundamentalGroupoid.map (overlapToLeft x₀ y₀ M N)).map
        (eK.unit.app z) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The inner right stage is literally the fundamental-groupoid map induced
by the overlap-to-right inclusion. -/
theorem genericPointWedgeIdentityOuterRightUnitInv_actualMap_eq_inclusionMap :
    let r := genericPointWedgeActualRight x₀ y₀ M N
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    r.map (eK.unitInv.app z) =
      (FundamentalGroupoid.map (overlapToRight x₀ y₀ M N)).map
        (eK.unitInv.app z) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The target endpoint of the left-span comparison at the transported
overlap representative is the literal left base object. -/
theorem genericPointWedgeIdentityOuterLeftSpanComponent_target :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (genericPointWedgeCoordinateLeft x₀).obj (eK.functor.obj z) =
      FundamentalGroupoid.mk x₀ := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The source endpoint of the left-span comparison retains the overlap
equivalence round trip before the actual-left and left-equivalence maps. -/
theorem genericPointWedgeIdentityOuterLeftSpanComponent_source_eq_nestedObj :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eL := genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let l := genericPointWedgeActualLeft x₀ y₀ M N
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (eK.inverse ⋙ l ⋙ eL.functor).obj (eK.functor.obj z) =
      eL.functor.obj (l.obj (eK.inverse.obj (eK.functor.obj z))) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The target endpoint of the right-span comparison at the transported
overlap representative is the literal right base object. -/
theorem genericPointWedgeIdentityOuterRightSpanComponent_target :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (genericPointWedgeCoordinateRight y₀).obj (eK.functor.obj z) =
      FundamentalGroupoid.mk y₀ := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The source endpoint of the right-span comparison retains the overlap
equivalence round trip before the actual-right and right-equivalence maps. -/
theorem genericPointWedgeIdentityOuterRightSpanComponent_source_eq_nestedObj :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eR := genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let r := genericPointWedgeActualRight x₀ y₀ M N
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (eK.inverse ⋙ r ⋙ eR.functor).obj (eK.functor.obj z) =
      eR.functor.obj (r.obj (eK.inverse.obj (eK.functor.obj z))) := by
  rfl

/-- The middle factor in the reverse coordinate glue evaluates at the image
of the chosen overlap representative under the overlap equivalence. -/
theorem genericPointWedgeIdentityCoordinateWhiskeredGlue_app :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (Functor.isoWhiskerLeft eK.functor Q.glue).hom.app z =
      Q.glue.hom.app (eK.functor.obj z) := by
  rfl

/-- At the chosen overlap representative, the whiskered middle factor is the
coordinate glue at the unique object of `FundamentalGroupoid Unit`. -/
theorem genericPointWedgeIdentityCoordinateWhiskeredGlue_app_eq_unitBase :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (Functor.isoWhiskerLeft eK.functor Q.glue).hom.app z =
      Q.glue.hom.app (FundamentalGroupoid.mk ()) := by
  dsimp only
  rw [genericPointWedgeIdentityCoordinateWhiskeredGlue_app]

/-- The coordinate glue at the unit base, expanded through the inverse
coordinate-to-point transport. -/
theorem genericPointWedgeIdentityCoordinateSpan_glue_unitBase :
    let l := genericPointWedgeCoordinateLeft x₀
    let r := genericPointWedgeCoordinateRight y₀
    let l' := pointLeg (FundamentalGroup X x₀)
    let r' := pointLeg (FundamentalGroup Y y₀)
    let eK := genericPointWedgeUnitSingleObjEquivalence
    let eL := genericPointWedgeSingleObjEquivalence x₀
    let eR := genericPointWedgeSingleObjEquivalence y₀
    let aL := genericPointWedgeCoordinateLeftPointIso x₀
    let aR := genericPointWedgeCoordinateRightPointIso y₀
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let z : FundamentalGroupoid Unit := FundamentalGroupoid.mk ()
    (genericPointWedgeIdentityCoordinateSpan x₀ y₀).glue.hom.app z =
      (reverseLeftComparison l l' eK eL aL Q.left).inv.app z ≫
        (Functor.isoWhiskerLeft eK.functor Q.glue).hom.app z ≫
          (reverseRightComparison r r' eK eR aR Q.right).hom.app z := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The central point-span glue factor is the identity element of the free
product at the unit base. -/
theorem genericPointWedgeIdentityPointSpan_whiskeredGlue_eq_one :
    let eK := genericPointWedgeUnitSingleObjEquivalence
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let z : FundamentalGroupoid Unit := FundamentalGroupoid.mk ()
    (Functor.isoWhiskerLeft eK.functor Q.glue).hom.app z =
      (1 : genericPointWedgeFreeProduct x₀ y₀) := by
  rfl

/-- After evaluating the point-span glue, the coordinate glue consists only
of the two connector comparison components. -/
theorem genericPointWedgeIdentityCoordinateSpan_glue_unitBase_eq_comparisons :
    let l := genericPointWedgeCoordinateLeft x₀
    let r := genericPointWedgeCoordinateRight y₀
    let l' := pointLeg (FundamentalGroup X x₀)
    let r' := pointLeg (FundamentalGroup Y y₀)
    let eK := genericPointWedgeUnitSingleObjEquivalence
    let eL := genericPointWedgeSingleObjEquivalence x₀
    let eR := genericPointWedgeSingleObjEquivalence y₀
    let aL := genericPointWedgeCoordinateLeftPointIso x₀
    let aR := genericPointWedgeCoordinateRightPointIso y₀
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let z : FundamentalGroupoid Unit := FundamentalGroupoid.mk ()
    (genericPointWedgeIdentityCoordinateSpan x₀ y₀).glue.hom.app z =
      (reverseLeftComparison l l' eK eL aL Q.left).inv.app z ≫
        (reverseRightComparison r r' eK eR aR Q.right).hom.app z := by
  dsimp only
  rw [genericPointWedgeIdentityCoordinateSpan_glue_unitBase,
    genericPointWedgeIdentityPointSpan_whiskeredGlue_eq_one]
  rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul,
    SingleObj.comp_as_mul]
  simp

omit [PathConnectedSpace Y] in
/-- The inverse left connector comparison at the unit base, expanded into the
Unit-equivalence round-trip component followed by the inverse leg comparison.
Neither component is normalized away. -/
theorem genericPointWedgeIdentityCoordinateLeftComparison_app :
    let l := genericPointWedgeCoordinateLeft x₀
    let l' := pointLeg (FundamentalGroup X x₀)
    let eK := genericPointWedgeUnitSingleObjEquivalence
    let eL := genericPointWedgeSingleObjEquivalence x₀
    let aL := genericPointWedgeCoordinateLeftPointIso x₀
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let z : FundamentalGroupoid Unit := FundamentalGroupoid.mk ()
    (reverseLeftComparison l l' eK eL aL Q.left).inv.app z =
      (Functor.isoWhiskerRight
          (eK.funInvIdAssoc (l ⋙ eL.functor)) Q.left).inv.app z ≫
        (Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft eK.functor aL.symm) Q.left).inv.app z := by
  rfl

omit [PathConnectedSpace X] in
/-- The right connector comparison at the unit base, expanded into the
right-leg comparison followed by the Unit-equivalence round-trip component.
Neither component is normalized away. -/
theorem genericPointWedgeIdentityCoordinateRightComparison_app :
    let r := genericPointWedgeCoordinateRight y₀
    let r' := pointLeg (FundamentalGroup Y y₀)
    let eK := genericPointWedgeUnitSingleObjEquivalence
    let eR := genericPointWedgeSingleObjEquivalence y₀
    let aR := genericPointWedgeCoordinateRightPointIso y₀
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let z : FundamentalGroupoid Unit := FundamentalGroupoid.mk ()
    (reverseRightComparison r r' eK eR aR Q.right).hom.app z =
      (Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft eK.functor aR.symm) Q.right).hom.app z ≫
        (Functor.isoWhiskerRight
          (eK.funInvIdAssoc (r ⋙ eR.functor)) Q.right).hom.app z := by
  rfl

omit [PathConnectedSpace Y] in
/-- The inverse left-leg factor is the identity at the unique unit-groupoid
base: its source comparison was constructed from subsingleton object equality. -/
theorem genericPointWedgeIdentityCoordinateLeftLegFactor_eq_one :
    let eK := genericPointWedgeUnitSingleObjEquivalence
    let aL := genericPointWedgeCoordinateLeftPointIso x₀
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let z : FundamentalGroupoid Unit := FundamentalGroupoid.mk ()
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft eK.functor aL.symm) Q.left).inv.app z =
        (1 : genericPointWedgeFreeProduct x₀ y₀) := by
  simp [genericPointWedgeCoordinateLeftPointIso,
    genericPointWedgeTrivialSourceFunctorIso]
  convert (genericPointWedgeIdentityPointSpan x₀ y₀).left.map_id _ using 1

omit [PathConnectedSpace X] in
/-- The right-leg factor is the identity at the unique unit-groupoid base:
its source comparison was constructed from subsingleton object equality. -/
theorem genericPointWedgeIdentityCoordinateRightLegFactor_eq_one :
    let eK := genericPointWedgeUnitSingleObjEquivalence
    let aR := genericPointWedgeCoordinateRightPointIso y₀
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let z : FundamentalGroupoid Unit := FundamentalGroupoid.mk ()
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft eK.functor aR.symm) Q.right).hom.app z =
        (1 : genericPointWedgeFreeProduct x₀ y₀) := by
  simp [genericPointWedgeCoordinateRightPointIso,
    genericPointWedgeTrivialSourceFunctorIso]
  convert (genericPointWedgeIdentityPointSpan x₀ y₀).right.map_id _ using 1

omit [PathConnectedSpace Y] in
/-- The inverse Unit round-trip factor is the identity at the unit-groupoid
base, using the subsingleton hom-set of `FundamentalGroupoid Unit`. -/
theorem genericPointWedgeIdentityCoordinateLeftRoundTrip_eq_one :
    let l := genericPointWedgeCoordinateLeft x₀
    let eK := genericPointWedgeUnitSingleObjEquivalence
    let eL := genericPointWedgeSingleObjEquivalence x₀
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let z : FundamentalGroupoid Unit := FundamentalGroupoid.mk ()
    (Functor.isoWhiskerRight
      (eK.funInvIdAssoc (l ⋙ eL.functor)) Q.left).inv.app z =
        (1 : genericPointWedgeFreeProduct x₀ y₀) := by
  have hunit : genericPointWedgeUnitSingleObjEquivalence.unit.app
      (FundamentalGroupoid.mk ()) = 𝟙 _ := Subsingleton.elim _ _
  simp [hunit]
  change (1 : genericPointWedgeFreeProduct x₀ y₀) = 1
  rfl

omit [PathConnectedSpace X] in
/-- The forward Unit round-trip factor is the identity at the unit-groupoid
base, using the subsingleton hom-set of `FundamentalGroupoid Unit`. -/
theorem genericPointWedgeIdentityCoordinateRightRoundTrip_eq_one :
    let r := genericPointWedgeCoordinateRight y₀
    let eK := genericPointWedgeUnitSingleObjEquivalence
    let eR := genericPointWedgeSingleObjEquivalence y₀
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let z : FundamentalGroupoid Unit := FundamentalGroupoid.mk ()
    (Functor.isoWhiskerRight
      (eK.funInvIdAssoc (r ⋙ eR.functor)) Q.right).hom.app z =
        (1 : genericPointWedgeFreeProduct x₀ y₀) := by
  have hunitInv : genericPointWedgeUnitSingleObjEquivalence.unitInv.app
      (FundamentalGroupoid.mk ()) = 𝟙 _ := Subsingleton.elim _ _
  simp [hunitInv]
  change (1 : genericPointWedgeFreeProduct x₀ y₀) = 1
  rfl

/-- All four connector-transport factors at the unit base cancel, so the
coordinate-span glue there is the unit of the free product. -/
theorem genericPointWedgeIdentityCoordinateSpan_glue_unitBase_eq_one :
    (genericPointWedgeIdentityCoordinateSpan x₀ y₀).glue.hom.app
        (FundamentalGroupoid.mk ()) =
      (1 : genericPointWedgeFreeProduct x₀ y₀) := by
  rw [genericPointWedgeIdentityCoordinateSpan_glue_unitBase_eq_comparisons,
    genericPointWedgeIdentityCoordinateLeftComparison_app,
    genericPointWedgeIdentityCoordinateRightComparison_app]
  rw [genericPointWedgeIdentityCoordinateLeftRoundTrip_eq_one,
    genericPointWedgeIdentityCoordinateLeftLegFactor_eq_one,
    genericPointWedgeIdentityCoordinateRightLegFactor_eq_one,
    genericPointWedgeIdentityCoordinateRightRoundTrip_eq_one]
  simp only [SingleObj.comp_as_mul, one_mul]

/-- After transporting the unit coordinate glue through the overlap
equivalence, the reverse-coordinate glue at the chosen overlap representative
is exactly the composite of the two outer span comparisons. -/
theorem genericPointWedgeIdentityCoordinateReverseSpan_glue_eq_outerComparisons :
    let l := genericPointWedgeActualLeft x₀ y₀ M N
    let r := genericPointWedgeActualRight x₀ y₀ M N
    let l' := genericPointWedgeCoordinateLeft x₀
    let r' := genericPointWedgeCoordinateRight y₀
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eL := genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eR := genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aL := genericPointWedgeLeftSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let aR := genericPointWedgeRightSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (genericPointWedgeIdentityCoordinateReverseSpan
      x₀ y₀ M N hM hN hy hx cM cN).glue.hom.app z =
      (reverseLeftComparison l l' eK eL aL Q.left).inv.app z ≫
        (reverseRightComparison r r' eK eR aR Q.right).hom.app z := by
  dsimp only
  rw [genericPointWedgeIdentityCoordinateReverseSpan_glue_app,
    genericPointWedgeIdentityCoordinateWhiskeredGlue_app_eq_unitBase,
    genericPointWedgeIdentityCoordinateSpan_glue_unitBase_eq_one]
  simp only [SingleObj.comp_as_mul, mul_one]

/-- The penultimate inverse stage of B3, now expressed as the literal
pseudococone on the two open pieces. -/
def genericPointWedgeIdentityPseudoCocone :
    PseudoFunctorCocone (X := Wedge x₀ y₀)
      (U := genericLeftOpen x₀ y₀ M)
      (V := genericRightOpen x₀ y₀ N)
      (C := SingleObj (genericPointWedgeFreeProduct x₀ y₀)) :=
  (genericPointWedgePseudoSpanEquivalence x₀ y₀ M N
    (SingleObj (genericPointWedgeFreeProduct x₀ y₀))).inverse.obj
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN)

def genericPointWedgeOpenCoverEquivalence (C : Type) [Category C] :
    (FundamentalGroupoid (Wedge x₀ y₀) ⥤ C) ≌
      PseudoFunctorCocone (X := Wedge x₀ y₀)
        (U := genericLeftOpen x₀ y₀ M)
        (V := genericRightOpen x₀ y₀ N) (C := C) :=
  twoOpenFundamentalGroupoidPseudopushoutEquivalence
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftOpen_isOpen
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightOpen_isOpen
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ

/-- The final inverse stage of B3: gluing the literal open-cover
pseudococone back to a functor on the wedge. -/
def genericPointWedgeIdentityGlobalFunctor :
    FundamentalGroupoid (Wedge x₀ y₀) ⥤
      SingleObj (genericPointWedgeFreeProduct x₀ y₀) :=
  (genericPointWedgeOpenCoverEquivalence
    x₀ y₀ M N hM hN hy hx cM cN
    (SingleObj (genericPointWedgeFreeProduct x₀ y₀))).inverse.obj
      (genericPointWedgeIdentityPseudoCocone
        x₀ y₀ M N hM hN hy hx cM cN)

@[simp] theorem genericPointWedgeIdentityPseudoCocone_left :
    (genericPointWedgeIdentityPseudoCocone
      x₀ y₀ M N hM hN hy hx cM cN).left =
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).left := rfl

@[simp] theorem genericPointWedgeIdentityPseudoCocone_right :
    (genericPointWedgeIdentityPseudoCocone
      x₀ y₀ M N hM hN hy hx cM cN).right =
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).right := rfl

@[simp] theorem genericPointWedgeIdentityPseudoCocone_glue :
    (genericPointWedgeIdentityPseudoCocone
      x₀ y₀ M N hM hN hy hx cM cN).glue =
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).glue := rfl

/-- The exact counit comparison between the restriction of the reconstructed
global functor and the supplied left cover-piece functor. -/
def genericPointWedgeIdentityGlobalLeftRestrictionIso :
    FundamentalGroupoid.map (TwoOpenDescentRestriction.coverPieceInclusion
      (U := genericLeftOpen x₀ y₀ M)
      (V := genericRightOpen x₀ y₀ N) true) ⋙
        genericPointWedgeIdentityGlobalFunctor
          x₀ y₀ M N hM hN hy hx cM cN ≅
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).left := by
  let e := genericPointWedgeOpenCoverEquivalence
    x₀ y₀ M N hM hN hy hx cM cN
    (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
  let P := genericPointWedgeIdentityPseudoCocone
    x₀ y₀ M N hM hN hy hx cM cN
  exact
    { hom := (e.counitIso.app P).hom.left
      inv := (e.counitIso.app P).inv.left
      hom_inv_id := by
        have h := congrArg (fun q => q.left) (e.counitIso.app P).hom_inv_id
        change (e.counitIso.app P).hom.left ≫
          (e.counitIso.app P).inv.left = 𝟙 _ at h
        exact h
      inv_hom_id := by
        have h := congrArg (fun q => q.left) (e.counitIso.app P).inv_hom_id
        change (e.counitIso.app P).inv.left ≫
          (e.counitIso.app P).hom.left = 𝟙 _ at h
        exact h }

/-- The corresponding counit comparison on the right cover piece. -/
def genericPointWedgeIdentityGlobalRightRestrictionIso :
    FundamentalGroupoid.map (TwoOpenDescentRestriction.coverPieceInclusion
      (U := genericLeftOpen x₀ y₀ M)
      (V := genericRightOpen x₀ y₀ N) false) ⋙
        genericPointWedgeIdentityGlobalFunctor
          x₀ y₀ M N hM hN hy hx cM cN ≅
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).right := by
  let e := genericPointWedgeOpenCoverEquivalence
    x₀ y₀ M N hM hN hy hx cM cN
    (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
  let P := genericPointWedgeIdentityPseudoCocone
    x₀ y₀ M N hM hN hy hx cM cN
  exact
    { hom := (e.counitIso.app P).hom.right
      inv := (e.counitIso.app P).inv.right
      hom_inv_id := by
        have h := congrArg (fun q => q.right) (e.counitIso.app P).hom_inv_id
        change (e.counitIso.app P).hom.right ≫
          (e.counitIso.app P).inv.right = 𝟙 _ at h
        exact h
      inv_hom_id := by
        have h := congrArg (fun q => q.right) (e.counitIso.app P).inv_hom_id
        change (e.counitIso.app P).inv.right ≫
          (e.counitIso.app P).hom.right = 𝟙 _ at h
        exact h }

theorem genericPointWedgeIdentityGlobalLeftRestriction_naturality
    {a b : FundamentalGroupoid (genericPointWedgeLeftPiece x₀ y₀ M)}
    (f : a ⟶ b) :
    (genericPointWedgeIdentityGlobalFunctor
        x₀ y₀ M N hM hN hy hx cM cN).map
          ((FundamentalGroupoid.map
            (TwoOpenDescentRestriction.coverPieceInclusion
              (U := genericLeftOpen x₀ y₀ M)
              (V := genericRightOpen x₀ y₀ N) true)).map f) ≫
      (genericPointWedgeIdentityGlobalLeftRestrictionIso
        x₀ y₀ M N hM hN hy hx cM cN).hom.app b =
    (genericPointWedgeIdentityGlobalLeftRestrictionIso
        x₀ y₀ M N hM hN hy hx cM cN).hom.app a ≫
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).left.map f :=
  (genericPointWedgeIdentityGlobalLeftRestrictionIso
    x₀ y₀ M N hM hN hy hx cM cN).hom.naturality f

theorem genericPointWedgeIdentityGlobalRightRestriction_naturality
    {a b : FundamentalGroupoid (genericPointWedgeRightPiece x₀ y₀ N)}
    (f : a ⟶ b) :
    (genericPointWedgeIdentityGlobalFunctor
        x₀ y₀ M N hM hN hy hx cM cN).map
          ((FundamentalGroupoid.map
            (TwoOpenDescentRestriction.coverPieceInclusion
              (U := genericLeftOpen x₀ y₀ M)
              (V := genericRightOpen x₀ y₀ N) false)).map f) ≫
      (genericPointWedgeIdentityGlobalRightRestrictionIso
        x₀ y₀ M N hM hN hy hx cM cN).hom.app b =
    (genericPointWedgeIdentityGlobalRightRestrictionIso
        x₀ y₀ M N hM hN hy hx cM cN).hom.app a ≫
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).right.map f :=
  (genericPointWedgeIdentityGlobalRightRestrictionIso
    x₀ y₀ M N hM hN hy hx cM cN).hom.naturality f

theorem genericPointWedgeIdentityGlobalLeftRestriction_hom_app
    (z : FundamentalGroupoid (genericPointWedgeLeftPiece x₀ y₀ M)) :
    (genericPointWedgeIdentityGlobalLeftRestrictionIso
      x₀ y₀ M N hM hN hy hx cM cN).hom.app z = 𝟙 _ := by
  rfl

def genericPointWedgeLeftBase :
    FundamentalGroupoid (genericPointWedgeLeftPiece x₀ y₀ M) :=
  FundamentalGroupoid.mk
    ⟨quotientMap x₀ y₀ (.inl x₀), ⟨.inl x₀, by trivial, rfl⟩⟩

theorem genericPointWedgeIdentityGlobalLeftRestriction_map
    {a b : FundamentalGroupoid (genericPointWedgeLeftPiece x₀ y₀ M)}
    (f : a ⟶ b) :
    (genericPointWedgeIdentityGlobalFunctor
        x₀ y₀ M N hM hN hy hx cM cN).map
          ((FundamentalGroupoid.map
            (TwoOpenDescentRestriction.coverPieceInclusion
              (U := genericLeftOpen x₀ y₀ M)
              (V := genericRightOpen x₀ y₀ N) true)).map f) =
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).left.map f := by
  have h := genericPointWedgeIdentityGlobalLeftRestriction_naturality
    x₀ y₀ M N hM hN hy hx cM cN f
  rw [genericPointWedgeIdentityGlobalLeftRestriction_hom_app,
    genericPointWedgeIdentityGlobalLeftRestriction_hom_app] at h
  calc
    _ = _ ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = 𝟙 _ ≫ _ := h
    _ = _ := Category.id_comp _

theorem genericPointWedgeIdentityGlobalLeftBase_map
    (f : End (genericPointWedgeLeftBase x₀ y₀ M)) :
    (genericPointWedgeIdentityGlobalFunctor
        x₀ y₀ M N hM hN hy hx cM cN).map
          ((FundamentalGroupoid.map
            (TwoOpenDescentRestriction.coverPieceInclusion
              (U := genericLeftOpen x₀ y₀ M)
              (V := genericRightOpen x₀ y₀ N) true)).map f) =
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).left.map f :=
  genericPointWedgeIdentityGlobalLeftRestriction_map
    x₀ y₀ M N hM hN hy hx cM cN f

/-- The right restriction component, retained as an explicit element because
it contains the overlap glue comparison. -/
def genericPointWedgeIdentityGlobalRightRestrictionElement
    (z : FundamentalGroupoid (genericPointWedgeRightPiece x₀ y₀ N)) :
    genericPointWedgeFreeProduct x₀ y₀ :=
  (genericPointWedgeIdentityGlobalRightRestrictionIso
    x₀ y₀ M N hM hN hy hx cM cN).hom.app z

/-- The right cover-piece presentation of the chosen (left) wedge-point
representative. -/
def genericPointWedgeRightBase :
    FundamentalGroupoid (genericPointWedgeRightPiece x₀ y₀ N) :=
  FundamentalGroupoid.mk
    ⟨quotientMap x₀ y₀ (.inl x₀), ⟨.inr y₀, by trivial,
      (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩

def genericPointWedgeOverlapBase : FundamentalGroupoid
    (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
  FundamentalGroupoid.mk
    ⟨quotientMap x₀ y₀ (.inl x₀),
      ⟨⟨.inl x₀, by trivial, rfl⟩,
        ⟨.inr y₀, by trivial,
          (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩

/-- The single right restriction element relevant to based loops. -/
def genericPointWedgeIdentityGlobalRightBaseElement :
    genericPointWedgeFreeProduct x₀ y₀ :=
  genericPointWedgeIdentityGlobalRightRestrictionElement
    x₀ y₀ M N hM hN hy hx cM cN
      (genericPointWedgeRightBase x₀ y₀ N)

/-- The part of the based right counit contributed by pseudococone
strictification, before the descent equivalence counit is composed with it. -/
def genericPointWedgeStrictificationRightBaseElement :
    genericPointWedgeFreeProduct x₀ y₀ :=
  (TwoOpenPseudoCoconeStrictification.pseudoCoconeStrictificationIso
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ
    (genericPointWedgeIdentityPseudoCocone
      x₀ y₀ M N hM hN hy hx cM cN)).inv.right.app
        (genericPointWedgeRightBase x₀ y₀ N)

theorem genericPointWedgeStrictificationRightBaseElement_eq_glue :
    genericPointWedgeStrictificationRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN =
      (genericPointWedgeIdentityPseudoCocone
        x₀ y₀ M N hM hN hy hx cM cN).glue.hom.app
          (genericPointWedgeOverlapBase x₀ y₀ M N) := by
  have hleft : quotientMap x₀ y₀ (.inl x₀) ∈
      genericLeftOpen x₀ y₀ M := ⟨.inl x₀, by trivial, rfl⟩
  simp [genericPointWedgeStrictificationRightBaseElement,
    TwoOpenPseudoCoconeStrictification.pseudoCoconeStrictificationIso,
    TwoOpenPseudoCoconeStrictification.pseudoCoconeStrictificationInv,
    pieceStrictificationIso, strictifiedObjectIso,
    genericPointWedgeRightBase, genericPointWedgeOverlapBase,
    genericLeftOpen, genericRightOpen, hleft]
  change 1 * _ * 1 = _
  simp
  congr 2

/-- The separate right-base factor contributed by the descent reconstruction
counit in the composite open-cover equivalence. -/
def genericPointWedgeDescentRightBaseElement :
    genericPointWedgeFreeProduct x₀ y₀ :=
  let hcover :=
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ
  let E := TwoOpenPseudoCoconeStrictification.twoOpenDescentPseudoCoconeEquivalence
    (C := SingleObj (genericPointWedgeFreeProduct x₀ y₀)) hcover
  let D := E.inverse.obj (genericPointWedgeIdentityPseudoCocone
    x₀ y₀ M N hM hN hy hx cM cN)
  (E.functor.map
    ((TwoOpenDescentCategory.twoOpenDescentEquivalence
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightOpen_isOpen
      hcover).counitIso.hom.app D)).right.app
        (genericPointWedgeRightBase x₀ y₀ N)

private theorem singleObj_eqToHom_eq_one_descent
    (G : Type) [Group G] {a b : SingleObj G} (h : a = b) :
    (eqToHom h : a ⟶ b) = (1 : G) := by
  subst b
  rfl

theorem genericPointWedgeDescentRightBaseElement_eq_one :
    genericPointWedgeDescentRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN = 1 := by
  dsimp [genericPointWedgeDescentRightBaseElement,
    TwoOpenPseudoCoconeStrictification.twoOpenDescentPseudoCoconeEquivalence,
    TwoOpenDescentCategory.twoOpenDescentEquivalence,
    TwoOpenDescentCategory.descentReconstructionIso,
    TwoOpenDescentCategory.descentReconstructionAppIso,
    TwoOpenDescentCategory.descentReconstructionHom,
    TwoOpenDescentRestriction.pieceRestrictionIso,
    TwoOpenDescentRestriction.restrictionAppIso,
    TwoOpenFundamentalGroupoidSpan.descentToPseudoCoconeFunctor,
    TwoOpenFundamentalGroupoidSpan.descentPseudoCoconeMap,
    CategoryTheory.Equivalence.mk]
  apply singleObj_eqToHom_eq_one_descent

theorem genericPointWedgeIdentityGlobalRightBaseElement_eq_strictification :
    genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN =
      genericPointWedgeStrictificationRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN := by
  simp [genericPointWedgeIdentityGlobalRightBaseElement,
    genericPointWedgeIdentityGlobalRightRestrictionElement,
    genericPointWedgeIdentityGlobalRightRestrictionIso,
    genericPointWedgeOpenCoverEquivalence,
    twoOpenFundamentalGroupoidPseudopushoutEquivalence,
    genericPointWedgeStrictificationRightBaseElement]
  change genericPointWedgeStrictificationRightBaseElement
      x₀ y₀ M N hM hN hy hx cM cN *
      genericPointWedgeDescentRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN = _
  rw [genericPointWedgeDescentRightBaseElement_eq_one]
  simp
  rfl

theorem genericPointWedgeIdentityGlobalRightBaseElement_eq_glue :
    genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN =
      (genericPointWedgeIdentityPseudoCocone
        x₀ y₀ M N hM hN hy hx cM cN).glue.hom.app
          (genericPointWedgeOverlapBase x₀ y₀ M N) :=
  (genericPointWedgeIdentityGlobalRightBaseElement_eq_strictification
    x₀ y₀ M N hM hN hy hx cM cN).trans
      (genericPointWedgeStrictificationRightBaseElement_eq_glue
        x₀ y₀ M N hM hN hy hx cM cN)

theorem genericPointWedgeIdentityGlobalRightBaseElement_eq_actualGlue :
    genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN =
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).glue.hom.app
          (genericPointWedgeOverlapBase x₀ y₀ M N) := by
  rw [genericPointWedgeIdentityGlobalRightBaseElement_eq_glue]
  rfl

theorem genericPointWedgeIdentityGlobalRightBaseElement_eq_coordinateReverseGlue :
    genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN =
      (genericPointWedgeIdentityCoordinateReverseSpan
        x₀ y₀ M N hM hN hy hx cM cN).glue.hom.app
          (genericPointWedgeOverlapBase x₀ y₀ M N) := by
  rw [genericPointWedgeIdentityGlobalRightBaseElement_eq_actualGlue]
  rfl

/-- The right reconstruction conjugator is the outer comparison composite:
the inner coordinate glue has already cancelled at the unique Unit object. -/
theorem genericPointWedgeIdentityGlobalRightBaseElement_eq_outerComparisons :
    let l := genericPointWedgeActualLeft x₀ y₀ M N
    let r := genericPointWedgeActualRight x₀ y₀ M N
    let l' := genericPointWedgeCoordinateLeft x₀
    let r' := genericPointWedgeCoordinateRight y₀
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eL := genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eR := genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aL := genericPointWedgeLeftSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let aR := genericPointWedgeRightSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z := genericPointWedgeOverlapBase x₀ y₀ M N
    genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN =
      (reverseLeftComparison l l' eK eL aL Q.left).inv.app z ≫
        (reverseRightComparison r r' eK eR aR Q.right).hom.app z := by
  dsimp only
  rw [genericPointWedgeIdentityGlobalRightBaseElement_eq_coordinateReverseGlue]
  simpa [genericPointWedgeOverlapBase] using
    (genericPointWedgeIdentityCoordinateReverseSpan_glue_eq_outerComparisons
      x₀ y₀ M N hM hN hy hx cM cN)

/-- Naturality solved for the reconstructed right-piece map.  The two
endpoint restriction components are deliberately visible. -/
theorem genericPointWedgeIdentityGlobalRightRestriction_map
    {a b : FundamentalGroupoid (genericPointWedgeRightPiece x₀ y₀ N)}
    (f : a ⟶ b) :
    (genericPointWedgeIdentityGlobalFunctor
        x₀ y₀ M N hM hN hy hx cM cN).map
          ((FundamentalGroupoid.map
            (TwoOpenDescentRestriction.coverPieceInclusion
              (U := genericLeftOpen x₀ y₀ M)
              (V := genericRightOpen x₀ y₀ N) false)).map f) =
      (genericPointWedgeIdentityGlobalRightRestrictionElement
          x₀ y₀ M N hM hN hy hx cM cN b)⁻¹ *
        (genericPointWedgeIdentityActualSpan
          x₀ y₀ M N hM hN hy hx cM cN).right.map f *
        genericPointWedgeIdentityGlobalRightRestrictionElement
          x₀ y₀ M N hM hN hy hx cM cN a := by
  have h := genericPointWedgeIdentityGlobalRightRestriction_naturality
    x₀ y₀ M N hM hN hy hx cM cN f
  change genericPointWedgeIdentityGlobalRightRestrictionElement
      x₀ y₀ M N hM hN hy hx cM cN b * _ = _ *
    genericPointWedgeIdentityGlobalRightRestrictionElement
        x₀ y₀ M N hM hN hy hx cM cN a at h
  apply mul_left_cancel (a :=
    genericPointWedgeIdentityGlobalRightRestrictionElement
      x₀ y₀ M N hM hN hy hx cM cN b)
  rw [h]
  simp [mul_assoc]

/-- At the wedge point the endpoint-dependent right restriction formula is
one inner conjugation. -/
theorem genericPointWedgeIdentityGlobalRightBase_map
    (f : End (genericPointWedgeRightBase x₀ y₀ N)) :
    (genericPointWedgeIdentityGlobalFunctor
        x₀ y₀ M N hM hN hy hx cM cN).map
          ((FundamentalGroupoid.map
            (TwoOpenDescentRestriction.coverPieceInclusion
              (U := genericLeftOpen x₀ y₀ M)
              (V := genericRightOpen x₀ y₀ N) false)).map f) =
      (genericPointWedgeIdentityGlobalRightBaseElement
          x₀ y₀ M N hM hN hy hx cM cN)⁻¹ *
        (genericPointWedgeIdentityActualSpan
          x₀ y₀ M N hM hN hy hx cM cN).right.map f *
        genericPointWedgeIdentityGlobalRightBaseElement
          x₀ y₀ M N hM hN hy hx cM cN :=
  genericPointWedgeIdentityGlobalRightRestriction_map
    x₀ y₀ M N hM hN hy hx cM cN f

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
@[simp] theorem genericPointWedgeIdentityRepresentation_inl
    (g : genericPointWedgeLeftGroup x₀) :
    (genericPointWedgeIdentityRepresentation x₀ y₀).action
        (Monoid.Coprod.inl g) = Monoid.Coprod.inl g := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
@[simp] theorem genericPointWedgeIdentityRepresentation_inr
    (g : genericPointWedgeRightGroup y₀) :
    (genericPointWedgeIdentityRepresentation x₀ y₀).action
        (Monoid.Coprod.inr g) = Monoid.Coprod.inr g := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
@[simp] theorem genericPointWedgeIdentityPointSpan_left
    (g : genericPointWedgeLeftGroup x₀) :
    (genericPointWedgeIdentityPointSpan x₀ y₀).left.map
        (X := SingleObj.star (genericPointWedgeLeftGroup x₀))
        (Y := SingleObj.star (genericPointWedgeLeftGroup x₀)) g =
      Monoid.Coprod.inl g := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
@[simp] theorem genericPointWedgeIdentityPointSpan_right
    (g : genericPointWedgeRightGroup y₀) :
    (genericPointWedgeIdentityPointSpan x₀ y₀).right.map
        (X := SingleObj.star (genericPointWedgeRightGroup y₀))
        (Y := SingleObj.star (genericPointWedgeRightGroup y₀)) g =
      Monoid.Coprod.inr g := by
  rfl

@[simp] theorem genericPointWedgeIdentityCoordinateSpan_left
    (g : FundamentalGroup X x₀) :
    (genericPointWedgeIdentityCoordinateSpan x₀ y₀).left.map
        (X := FundamentalGroupoid.mk x₀)
        (Y := FundamentalGroupoid.mk x₀) g = Monoid.Coprod.inl g := by
  change (genericPointWedgeIdentityPointSpan x₀ y₀).left.map
      ((genericPointWedgeSingleObjEquivalence x₀).functor.map g) = _
  rw [show (genericPointWedgeSingleObjEquivalence x₀).functor.map g = g by
    simp [genericPointWedgeSingleObjEquivalence, genericPointWedgeConnectors,
      ConnectorSystem.normalForm]]
  exact genericPointWedgeIdentityPointSpan_left x₀ y₀ g

/-- On arbitrary endpoints, the coordinate left functor applies the connector
normal form before injecting into the free product. -/
theorem genericPointWedgeIdentityCoordinateSpan_left_map
    {a b : FundamentalGroupoid X} (f : a ⟶ b) :
    HEq ((genericPointWedgeIdentityCoordinateSpan x₀ y₀).left.map f)
      ((Monoid.Coprod.inl ((genericPointWedgeConnectors x₀).normalForm f)) :
        genericPointWedgeFreeProduct x₀ y₀) := by
  change HEq ((genericPointWedgeIdentityPointSpan x₀ y₀).left.map
      ((genericPointWedgeSingleObjEquivalence x₀).functor.map f)) _
  rw [show (genericPointWedgeSingleObjEquivalence x₀).functor.map f =
      (genericPointWedgeConnectors x₀).normalForm f by
    rfl]
  exact heq_of_eq (genericPointWedgeIdentityPointSpan_left x₀ y₀ _)

@[simp] theorem genericPointWedgeIdentityCoordinateSpan_right
    (g : FundamentalGroup Y y₀) :
    (genericPointWedgeIdentityCoordinateSpan x₀ y₀).right.map
        (X := FundamentalGroupoid.mk y₀)
        (Y := FundamentalGroupoid.mk y₀) g = Monoid.Coprod.inr g := by
  change (genericPointWedgeIdentityPointSpan x₀ y₀).right.map
      ((genericPointWedgeSingleObjEquivalence y₀).functor.map g) = _
  rw [show (genericPointWedgeSingleObjEquivalence y₀).functor.map g = g by
    simp [genericPointWedgeSingleObjEquivalence, genericPointWedgeConnectors,
      ConnectorSystem.normalForm]]
  exact genericPointWedgeIdentityPointSpan_right x₀ y₀ g

/-- On arbitrary endpoints, the coordinate right functor applies the connector
normal form before injecting into the free product. -/
theorem genericPointWedgeIdentityCoordinateSpan_right_map
    {a b : FundamentalGroupoid Y} (f : a ⟶ b) :
    HEq ((genericPointWedgeIdentityCoordinateSpan x₀ y₀).right.map f)
      ((Monoid.Coprod.inr ((genericPointWedgeConnectors y₀).normalForm f)) :
        genericPointWedgeFreeProduct x₀ y₀) := by
  change HEq ((genericPointWedgeIdentityPointSpan x₀ y₀).right.map
      ((genericPointWedgeSingleObjEquivalence y₀).functor.map f)) _
  rw [show (genericPointWedgeSingleObjEquivalence y₀).functor.map f =
      (genericPointWedgeConnectors y₀).normalForm f by
    rfl]
  exact heq_of_eq (genericPointWedgeIdentityPointSpan_right x₀ y₀ _)

/-- The exact outer left-span component maps to the left coproduct injection
of its connector normal form. -/
theorem genericPointWedgeIdentityOuterLeftSpanMap_heq_inl_normalForm :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aL := genericPointWedgeLeftSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    HEq (Q.left.map (aL.hom.app (eK.functor.obj z)))
      ((Monoid.Coprod.inl ((genericPointWedgeConnectors x₀).normalForm
        (aL.hom.app (eK.functor.obj z)))) :
          genericPointWedgeFreeProduct x₀ y₀) := by
  exact genericPointWedgeIdentityCoordinateSpan_left_map x₀ y₀ _

/-- The exact outer right-span component maps to the right coproduct injection
of its connector normal form. -/
theorem genericPointWedgeIdentityOuterRightSpanMap_heq_inr_normalForm :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aR := genericPointWedgeRightSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    HEq (Q.right.map (aR.inv.app (eK.functor.obj z)))
      ((Monoid.Coprod.inr ((genericPointWedgeConnectors y₀).normalForm
        (aR.inv.app (eK.functor.obj z)))) :
          genericPointWedgeFreeProduct x₀ y₀) := by
  exact genericPointWedgeIdentityCoordinateSpan_right_map x₀ y₀ _

omit [PathConnectedSpace Y] in
/-- Expand the left outer component's connector normal form into its three
ordered factors, without rewriting either dependent endpoint. -/
theorem genericPointWedgeIdentityOuterLeftSpan_normalForm_eq_connectors :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aL := genericPointWedgeLeftSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (genericPointWedgeConnectors x₀).normalForm
        (aL.hom.app (eK.functor.obj z)) =
      ((genericPointWedgeConnectors x₀).connector
          ((eK.inverse ⋙ genericPointWedgeActualLeft x₀ y₀ M N ⋙
            (genericPointWedgeLeftGroupoidEquivalence
              x₀ y₀ M N hM hN hy hx cM cN).functor).obj
                (eK.functor.obj z))).hom ≫
        aL.hom.app (eK.functor.obj z) ≫
        ((genericPointWedgeConnectors x₀).connector
          ((genericPointWedgeCoordinateLeft x₀).obj
            (eK.functor.obj z))).inv := by
  rfl

omit [PathConnectedSpace X] in
/-- Expand the right outer inverse component's connector normal form into its
three ordered factors, without rewriting either dependent endpoint. -/
theorem genericPointWedgeIdentityOuterRightSpan_normalForm_eq_connectors :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aR := genericPointWedgeRightSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (genericPointWedgeConnectors y₀).normalForm
        (aR.inv.app (eK.functor.obj z)) =
      ((genericPointWedgeConnectors y₀).connector
          ((genericPointWedgeCoordinateRight y₀).obj
            (eK.functor.obj z))).hom ≫
        aR.inv.app (eK.functor.obj z) ≫
        ((genericPointWedgeConnectors y₀).connector
          ((eK.inverse ⋙ genericPointWedgeActualRight x₀ y₀ M N ⋙
            (genericPointWedgeRightGroupoidEquivalence
              x₀ y₀ M N hM hN hy hx cM cN).functor).obj
                (eK.functor.obj z))).inv := by
  rfl

omit [PathConnectedSpace Y] in
/-- The terminal connector in the left outer normal form is the reflexive
connector at the literal left base object, stated heterogeneously so that no
dependent arrow is cast away. -/
theorem genericPointWedgeIdentityOuterLeftSpan_targetConnector_heq_refl :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    HEq ((genericPointWedgeConnectors x₀).connector
        ((genericPointWedgeCoordinateLeft x₀).obj (eK.functor.obj z)))
      (Iso.refl (FundamentalGroupoid.mk x₀)) := by
  dsimp only
  rw [genericPointWedgeIdentityOuterLeftSpanComponent_target
    x₀ y₀ M N hM hN hy hx cM cN]
  exact heq_of_eq (genericPointWedgeBasedConnector_base x₀)

omit [PathConnectedSpace X] in
/-- The source connector for the right outer inverse component is reflexive
at the literal right base object, again retaining its dependent object type. -/
theorem genericPointWedgeIdentityOuterRightSpan_sourceConnector_heq_refl :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    HEq ((genericPointWedgeConnectors y₀).connector
        ((genericPointWedgeCoordinateRight y₀).obj (eK.functor.obj z)))
      (Iso.refl (FundamentalGroupoid.mk y₀)) := by
  dsimp only
  rw [genericPointWedgeIdentityOuterRightSpanComponent_target
    x₀ y₀ M N hM hN hy hx cM cN]
  exact heq_of_eq (genericPointWedgeBasedConnector_base y₀)

omit [PathConnectedSpace Y] in
/-- The remaining source connector in the left outer normal form is exactly
the chosen based connector at the transported overlap object. -/
theorem genericPointWedgeIdentityOuterLeftSpan_sourceConnector_eq_based :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (genericPointWedgeConnectors x₀).connector
        ((eK.inverse ⋙ genericPointWedgeActualLeft x₀ y₀ M N ⋙
          (genericPointWedgeLeftGroupoidEquivalence
            x₀ y₀ M N hM hN hy hx cM cN).functor).obj
              (eK.functor.obj z)) =
      genericPointWedgeBasedConnector x₀
        ((eK.inverse ⋙ genericPointWedgeActualLeft x₀ y₀ M N ⋙
          (genericPointWedgeLeftGroupoidEquivalence
            x₀ y₀ M N hM hN hy hx cM cN).functor).obj
              (eK.functor.obj z)) := by
  rfl

omit [PathConnectedSpace X] in
/-- The remaining target connector for the right outer inverse component is
exactly the chosen based connector at the transported overlap object. -/
theorem genericPointWedgeIdentityOuterRightSpan_targetConnector_eq_based :
    let eK := genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let z : FundamentalGroupoid (genericPointWedgeOverlapPiece x₀ y₀ M N) :=
      FundamentalGroupoid.mk
        ⟨quotientMap x₀ y₀ (.inl x₀),
          ⟨⟨.inl x₀, by trivial, rfl⟩,
            ⟨.inr y₀, by trivial,
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm⟩⟩⟩
    (genericPointWedgeConnectors y₀).connector
        ((eK.inverse ⋙ genericPointWedgeActualRight x₀ y₀ M N ⋙
          (genericPointWedgeRightGroupoidEquivalence
            x₀ y₀ M N hM hN hy hx cM cN).functor).obj
              (eK.functor.obj z)) =
      genericPointWedgeBasedConnector y₀
        ((eK.inverse ⋙ genericPointWedgeActualRight x₀ y₀ M N ⋙
          (genericPointWedgeRightGroupoidEquivalence
            x₀ y₀ M N hM hN hy hx cM cN).functor).obj
              (eK.functor.obj z)) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The literal overlap-to-left inclusion sends the chosen overlap base
object to the chosen left cover base object. -/
theorem genericPointWedgeOverlapToLeft_obj_overlapBase :
    (FundamentalGroupoid.map (overlapToLeft x₀ y₀ M N)).obj
        (genericPointWedgeOverlapBase x₀ y₀ M N) =
      genericPointWedgeLeftBase x₀ y₀ M := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The literal overlap-to-right inclusion sends the chosen overlap base
object to the chosen right cover base object. -/
theorem genericPointWedgeOverlapToRight_obj_overlapBase :
    (FundamentalGroupoid.map (overlapToRight x₀ y₀ M N)).obj
        (genericPointWedgeOverlapBase x₀ y₀ M N) =
      genericPointWedgeRightBase x₀ y₀ N := by
  rfl

/-- The literal left wedge leg, lifted to the left member of the open cover. -/
def genericPointWedgeLeftLegLift :
    C(X, genericPointWedgeLeftPiece x₀ y₀ M) where
  toFun x :=
    ⟨quotientMap x₀ y₀ (.inl x), ⟨.inl x, by trivial, rfl⟩⟩
  continuous_toFun :=
    ((continuous_quotientMap x₀ y₀).comp continuous_inl).subtype_mk _

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The lifted left leg is based at the literal left cover representative. -/
theorem genericPointWedgeLeftLegLift_base :
    FundamentalGroupoid.mk (genericPointWedgeLeftLegLift x₀ y₀ M x₀) =
      genericPointWedgeLeftBase x₀ y₀ M := by
  rfl

/-- The literal right wedge leg, lifted to the right member of the open cover. -/
def genericPointWedgeRightLegLift :
    C(Y, genericPointWedgeRightPiece x₀ y₀ N) where
  toFun y :=
    ⟨quotientMap x₀ y₀ (.inr y), ⟨.inr y, by trivial, rfl⟩⟩
  continuous_toFun :=
    ((continuous_quotientMap x₀ y₀).comp continuous_inr).subtype_mk _

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The lifted right leg at `y₀` is the fixed right cover base object; this is
the first place the quotient relation identifies the two wedge representatives. -/
theorem genericPointWedgeRightLegLift_base :
    FundamentalGroupoid.mk (genericPointWedgeRightLegLift x₀ y₀ N y₀) =
      genericPointWedgeRightBase x₀ y₀ N := by
  apply congrArg FundamentalGroupoid.mk
  apply Subtype.ext
  exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

/-- A based loop in the left summand, lifted as an endomorphism of the fixed
left-cover base object. -/
def genericPointWedgeLeftLiftedLoop
    (g : FundamentalGroup X x₀) :
    End (genericPointWedgeLeftBase x₀ y₀ M) :=
  FundamentalGroup.map (genericPointWedgeLeftLegLift x₀ y₀ M) x₀ g

/-- A based loop in the right summand, lifted to the fixed right-cover base;
`mapOfEq` records precisely the quotient equality between representatives. -/
def genericPointWedgeRightLiftedLoop
    (g : FundamentalGroup Y y₀) :
    End (genericPointWedgeRightBase x₀ y₀ N) :=
  FundamentalGroup.mapOfEq (genericPointWedgeRightLegLift x₀ y₀ N)
    (by
      apply Subtype.ext
      exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm) g

theorem genericPointWedgeIdentityActualSpan_left_map
    {a b : FundamentalGroupoid (genericPointWedgeLeftPiece x₀ y₀ M)}
    (f : a ⟶ b) :
    (genericPointWedgeIdentityActualSpan
      x₀ y₀ M N hM hN hy hx cM cN).left.map f =
      (genericPointWedgeIdentityCoordinateSpan x₀ y₀).left.map
        ((genericPointWedgeLeftGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map f) := by
  rfl

theorem genericPointWedgeIdentityActualSpan_right_map
    {a b : FundamentalGroupoid (genericPointWedgeRightPiece x₀ y₀ N)}
    (f : a ⟶ b) :
    (genericPointWedgeIdentityActualSpan
      x₀ y₀ M N hM hN hy hx cM cN).right.map f =
      (genericPointWedgeIdentityCoordinateSpan x₀ y₀).right.map
        ((genericPointWedgeRightGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map f) := by
  rfl

variable {C D : Type} [Category C] [Category D]

private abbrev genericSpanPostcompose (K : C ⥤ D) :=
  FreeProductPointSpanRepresentations.postcomposeRepresentationFunctor
    (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) K

private abbrev genericSingleObjPostcompose (K : C ⥤ D) :=
  FreeProductRepresentationSingleObjEquivalence.postcomposeRepresentationFunctor
    (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) K

def genericPointWedgeRepresentationAlignmentApp (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C)
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀)) :
    (genericSpanPostcompose x₀ y₀ K).obj R ≅
      (genericSingleObjPostcompose x₀ y₀ K).obj R where
  hom := ⟨𝟙 _, by
    intro g
    change mappedAction _ _ K R g ≫ 𝟙 _ = 𝟙 _ ≫ mappedAction _ _ K R g
    simp⟩
  inv := ⟨𝟙 _, by
    intro g
    change mappedAction _ _ K R g ≫ 𝟙 _ = 𝟙 _ ≫ mappedAction _ _ K R g
    simp⟩
  hom_inv_id := by apply FreeProductRepresentationHom.ext; exact Category.id_comp _
  inv_hom_id := by apply FreeProductRepresentationHom.ext; exact Category.id_comp _

def genericPointWedgeRepresentationAlignment (K : C ⥤ D) :
    genericSpanPostcompose x₀ y₀ K ≅
      genericSingleObjPostcompose x₀ y₀ K :=
  NatIso.ofComponents (genericPointWedgeRepresentationAlignmentApp x₀ y₀ K) (by
    intro R S f
    apply FreeProductRepresentationHom.ext
    change K.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ K.map f.hom
    simp)

def genericPointWedgePseudoSpanPostcomposeIso (K : C ⥤ D) :
    postcomposePseudoFunctorCoconeFunctor K ⋙
        (genericPointWedgePseudoSpanEquivalence x₀ y₀ M N D).functor ≅
      (genericPointWedgePseudoSpanEquivalence x₀ y₀ M N C).functor ⋙
        postcomposeFunctor K :=
  eqToIso (by rfl)

@[reducible] def genericPointWedgeOpenCoverSquare (K : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight (FundamentalGroupoid (Wedge x₀ y₀)) C D).obj K)
    (twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C)
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ).functor
    (twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := D)
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightOpen_isOpen
      (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ).functor
    (postcomposePseudoFunctorCoconeFunctor K) where
  iso := pseudopushoutPostcomposeNatIso
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftOpen_isOpen
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightOpen_isOpen
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).union_eq_univ K

@[reducible] def genericPointWedgeAlignmentSquare (K : C ⥤ D) : CatCommSq
    (genericSpanPostcompose x₀ y₀ K)
    (𝟭 (FreeProductRepresentation (C := C)
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀)))
    (𝟭 (FreeProductRepresentation (C := D)
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀)))
    (genericSingleObjPostcompose x₀ y₀ K) where
  iso := (Functor.rightUnitor _).trans
    ((genericPointWedgeRepresentationAlignment x₀ y₀ K).trans
      (Functor.leftUnitor _).symm)

@[reducible] def genericPointWedgeSingleObjSquare (K : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight (FundamentalGroupoid (Wedge x₀ y₀)) C D).obj K)
    (genericPointWedgeSingleObjMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C).functor
    (genericPointWedgeSingleObjMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN D).functor
    ((Functor.whiskeringRight
      (SingleObj (genericPointWedgeFreeProduct x₀ y₀)) C D).obj K) := by
  let s0 := genericPointWedgeOpenCoverSquare x₀ y₀ M N hM hN hy hx cM cN K
  let s1 : CatCommSq _
      (genericPointWedgePseudoSpanEquivalence x₀ y₀ M N C).functor
      (genericPointWedgePseudoSpanEquivalence x₀ y₀ M N D).functor
      (postcomposeFunctor K) :=
    ⟨genericPointWedgePseudoSpanPostcomposeIso x₀ y₀ M N K⟩
  let s2 : CatCommSq (postcomposeFunctor K)
      (genericPointWedgeCoordinateSpanEquivalence
        x₀ y₀ M N hM hN hy hx cM cN C).functor
      (genericPointWedgeCoordinateSpanEquivalence
        x₀ y₀ M N hM hN hy hx cM cN D).functor
      (postcomposeFunctor K) :=
    ⟨genericPointWedgeCoordinateSpanPostcomposeIso
      x₀ y₀ M N hM hN hy hx cM cN K⟩
  let s3 : CatCommSq (postcomposeFunctor K)
      (genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C).functor
      (genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ D).functor
      (postcomposeFunctor K) :=
    ⟨genericPointWedgeCoordinatePointSpanPostcomposeIso x₀ y₀ K⟩
  let s4 : CatCommSq (postcomposeFunctor K)
      (freeProductPointSpanEquivalence
        (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C).functor
      (freeProductPointSpanEquivalence
        (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) D).functor
      (genericSpanPostcompose x₀ y₀ K) :=
    ⟨FreeProductPointSpanRepresentations.equivalenceFunctorPostcomposeIso
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) K⟩
  let s5 := genericPointWedgeAlignmentSquare x₀ y₀ K
  let s6 : CatCommSq (genericSingleObjPostcompose x₀ y₀ K)
      (representationSingleObjEquivalence (C := C)
        (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀)).functor
      (representationSingleObjEquivalence (C := D)
        (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀)).functor _ :=
    ⟨representationToFunctorPostcomposeIso
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) K⟩
  exact CatCommSq.vComp' (CatCommSq.vComp'
    (CatCommSq.vComp' (CatCommSq.vComp' (CatCommSq.vComp' s0 s1) s2) s3) s4)
    (CatCommSq.vComp' s5 s6)

def genericPointWedgeSingleObjPostcomposeIso (K : C ⥤ D) :=
  (genericPointWedgeSingleObjSquare
    x₀ y₀ M N hM hN hy hx cM cN K).iso

end GenericSingleObjMapping

section GenericSourceEquivalence

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [PathConnectedSpace X] [PathConnectedSpace Y]
variable (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
variable (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
variable (cM : PointedContraction M ⟨y₀, hy⟩)
variable (cN : PointedContraction N ⟨x₀, hx⟩)

/-- The source groupoid equivalence reconstructed from the target-natural
point-wedge mapping equivalences. -/
def genericPointWedgeSourceEquivalence :
    FundamentalGroupoid (Wedge x₀ y₀) ≌
      SingleObj (genericPointWedgeFreeProduct x₀ y₀) :=
  GenericTargetNaturalSourceReconstruction.sourceEquivalence
    (fun C _ => genericPointWedgeSingleObjMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C)
    (fun K => genericPointWedgeSingleObjPostcomposeIso
      x₀ y₀ M N hM hN hy hx cM cN K)

end GenericSourceEquivalence

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

private theorem singleObj_eqToHom_eq_one
    {G : Type u} [Group G] {A B : SingleObj G} (h : A = B) :
    (eqToHom h : A ⟶ B) = (1 : G) := by
  cases A
  cases B
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl

/-- Evaluation of the representation-independent B5 extraction is the map
on endomorphisms of the underlying equivalence functor. -/
theorem fundamentalGroupMulEquivOfSingleObjEquivalence_apply
    {X : Type u} [TopologicalSpace X] (x : X) (G : Type u) [Group G]
    (E : FundamentalGroupoid X ≌ SingleObj G) (g : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfSingleObjEquivalence x G E g = E.functor.map g := by
  change (eqToIso (Subsingleton.elim
      (E.functor.obj (FundamentalGroupoid.mk x)) (SingleObj.star G))).inv ≫
      E.functor.map g ≫
      (eqToIso (Subsingleton.elim
        (E.functor.obj (FundamentalGroupoid.mk x)) (SingleObj.star G))).hom = _
  rw [eqToIso.inv, eqToIso.hom, singleObj_eqToHom_eq_one,
    singleObj_eqToHom_eq_one]
  rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul]
  simp

section GenericFundamentalGroupEquivalence

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [PathConnectedSpace X] [PathConnectedSpace Y]
variable (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
variable (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
variable (cM : PointedContraction M ⟨y₀, hy⟩)
variable (cN : PointedContraction N ⟨x₀, hx⟩)

/-- The based fundamental-group equivalence underlying the literal B6 leg
coordinate calculation. -/
def genericPointWedgeFundamentalGroupEquiv :
    FundamentalGroup (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀)) ≃*
      genericPointWedgeFreeProduct x₀ y₀ :=
  fundamentalGroupMulEquivOfSingleObjEquivalence
    (quotientMap x₀ y₀ (.inl x₀))
    (genericPointWedgeFreeProduct x₀ y₀)
    (genericPointWedgeSourceEquivalence x₀ y₀ M N hM hN hy hx cM cN)

theorem genericPointWedgeFundamentalGroupEquiv_apply
    (g : FundamentalGroup (Wedge x₀ y₀)
      (quotientMap x₀ y₀ (.inl x₀))) :
    genericPointWedgeFundamentalGroupEquiv
        x₀ y₀ M N hM hN hy hx cM cN g =
      (genericPointWedgeSourceEquivalence
        x₀ y₀ M N hM hN hy hx cM cN).functor.map g :=
  fundamentalGroupMulEquivOfSingleObjEquivalence_apply _ _ _ g

private abbrev genericPointWedgeTarget :=
  SingleObj (genericPointWedgeFreeProduct x₀ y₀)

/-- The reconstructed forward functor is definitionally the inverse image of
the identity under the B3 mapping equivalence. -/
theorem genericPointWedgeSourceFunctor_eq_inverse_identity :
    (genericPointWedgeSourceEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor =
      (genericPointWedgeSingleObjMappingEquivalence
        x₀ y₀ M N hM hN hy hx cM cN
        (genericPointWedgeTarget x₀ y₀)).inverse.obj
          (𝟭 (genericPointWedgeTarget x₀ y₀)) :=
  rfl

/-- The exact B3 inverse object whose action on the two literal wedge legs is
the remaining B6 computation. -/
def genericPointWedgeInverseIdentityFunctor :
    FundamentalGroupoid (Wedge x₀ y₀) ⥤ genericPointWedgeTarget x₀ y₀ :=
  (genericPointWedgeSingleObjMappingEquivalence
    x₀ y₀ M N hM hN hy hx cM cN
    (genericPointWedgeTarget x₀ y₀)).inverse.obj
      (𝟭 (genericPointWedgeTarget x₀ y₀))

/-- Unfolding the composite B3 inverse reaches exactly the named global
functor reconstructed from the literal open-cover pseudococone. -/
theorem genericPointWedgeInverseIdentityFunctor_eq_global :
    genericPointWedgeInverseIdentityFunctor
      x₀ y₀ M N hM hN hy hx cM cN =
      genericPointWedgeIdentityGlobalFunctor
        x₀ y₀ M N hM hN hy hx cM cN := rfl

theorem genericPointWedgeSourceFunctor_map_eq_inverseIdentity
    {a b : FundamentalGroupoid (Wedge x₀ y₀)} (g : a ⟶ b) :
    (genericPointWedgeSourceEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor.map g =
      (genericPointWedgeInverseIdentityFunctor
        x₀ y₀ M N hM hN hy hx cM cN).map g := by
  rw [genericPointWedgeSourceFunctor_eq_inverse_identity]
  rfl

/-- The counit available for the B6 coordinate calculation.  Its naturality,
rather than an invalid identity normalization, controls the generator maps. -/
def genericPointWedgeSourceCounit :
    (genericPointWedgeSingleObjMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
      (genericPointWedgeTarget x₀ y₀)).functor.obj
        (genericPointWedgeSourceEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor ≅
      𝟭 (genericPointWedgeTarget x₀ y₀) :=
  (genericPointWedgeSingleObjMappingEquivalence
    x₀ y₀ M N hM hN hy hx cM cN
    (genericPointWedgeTarget x₀ y₀)).counitIso.app _

theorem genericPointWedgeSourceCounit_naturality
    (g : End (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀))) :
    ((genericPointWedgeSingleObjMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
      (genericPointWedgeTarget x₀ y₀)).functor.obj
        (genericPointWedgeSourceEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor).map g ≫
        (genericPointWedgeSourceCounit
          x₀ y₀ M N hM hN hy hx cM cN).hom.app _ =
      (genericPointWedgeSourceCounit
        x₀ y₀ M N hM hN hy hx cM cN).hom.app _ ≫ g :=
  (genericPointWedgeSourceCounit
    x₀ y₀ M N hM hN hy hx cM cN).hom.naturality g

theorem genericPointWedgeSourceCounit_left
    (g : FundamentalGroup X x₀) :
    ((genericPointWedgeSingleObjMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
      (genericPointWedgeTarget x₀ y₀)).functor.obj
        (genericPointWedgeSourceEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor).map
          (Monoid.Coprod.inl g : End (SingleObj.star
            (genericPointWedgeFreeProduct x₀ y₀))) ≫
        (genericPointWedgeSourceCounit
          x₀ y₀ M N hM hN hy hx cM cN).hom.app
            (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀)) =
      (genericPointWedgeSourceCounit
        x₀ y₀ M N hM hN hy hx cM cN).hom.app
          (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀)) ≫
            (Monoid.Coprod.inl g : End (SingleObj.star
              (genericPointWedgeFreeProduct x₀ y₀))) :=
  genericPointWedgeSourceCounit_naturality
    x₀ y₀ M N hM hN hy hx cM cN (Monoid.Coprod.inl g)

theorem genericPointWedgeSourceCounit_right
    (g : FundamentalGroup Y y₀) :
    ((genericPointWedgeSingleObjMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
      (genericPointWedgeTarget x₀ y₀)).functor.obj
        (genericPointWedgeSourceEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor).map
          (Monoid.Coprod.inr g : End (SingleObj.star
            (genericPointWedgeFreeProduct x₀ y₀))) ≫
        (genericPointWedgeSourceCounit
          x₀ y₀ M N hM hN hy hx cM cN).hom.app
            (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀)) =
      (genericPointWedgeSourceCounit
        x₀ y₀ M N hM hN hy hx cM cN).hom.app
          (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀)) ≫
            (Monoid.Coprod.inr g : End (SingleObj.star
              (genericPointWedgeFreeProduct x₀ y₀))) :=
  genericPointWedgeSourceCounit_naturality
    x₀ y₀ M N hM hN hy hx cM cN (Monoid.Coprod.inr g)

def genericPointWedgeCounitElement : genericPointWedgeFreeProduct x₀ y₀ :=
  (genericPointWedgeSourceCounit
    x₀ y₀ M N hM hN hy hx cM cN).hom.app
      (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀))

/-- The B3 counit splits at its final representation-to-single-object stage.
This exposes the remaining comparison as one mapped free-product-representation
counit followed by the final representation counit. -/
theorem genericPointWedgeCounitElement_eq_representationCounits :
    let C := genericPointWedgeTarget x₀ y₀
    let E := genericPointWedgeFreeProductMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN =
      (R.functor.map (E.counitIso.hom.app (R.inverse.obj F))).app
          (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀)) ≫
        (R.counitIso.hom.app F).app
          (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀)) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The final representation-to-single-object counit contributes the unit at
the unique target object. -/
theorem genericPointWedgeRepresentationCounit_app_eq_one :
    let C := genericPointWedgeTarget x₀ y₀
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    (R.counitIso.hom.app F).app
        (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀)) =
      (1 : genericPointWedgeFreeProduct x₀ y₀) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The counit of the final point-span-to-free-product stage is the identity
on the target of the identity representation. -/
theorem genericPointWedgePointSpanCounit_hom_eq_id :
    let C := genericPointWedgeTarget x₀ y₀
    let Q := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    (Q.counitIso.hom.app (R.inverse.obj F)).hom =
      𝟙 (R.inverse.obj F).target := by
  simp

/-- The counit of the free-product mapping equivalence splits into the mapped
pre-free-product counit followed by the final point-span counit. -/
theorem genericPointWedgeFreeProductCounit_eq_pre_pointSpan :
    let C := genericPointWedgeTarget x₀ y₀
    let P := genericPointWedgePreFreeProductMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let Q := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    ((P.trans Q).counitIso.hom.app (R.inverse.obj F)) =
      Q.functor.map
          (P.counitIso.hom.app (Q.inverse.obj (R.inverse.obj F))) ≫
        Q.counitIso.hom.app (R.inverse.obj F) := by
  rfl

/-- The pre-free-product counit splits once more at the final
coordinate-to-point-span stage. -/
theorem genericPointWedgePreFreeProductCounit_eq_preCoordinate_coordinatePoint :
    let C := genericPointWedgeTarget x₀ y₀
    let P := genericPointWedgePreCoordinatePointSpanMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    let S := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    ((P.trans Q).counitIso.hom.app (S.inverse.obj (R.inverse.obj F))) =
      Q.functor.map
          (P.counitIso.hom.app
            (Q.inverse.obj (S.inverse.obj (R.inverse.obj F)))) ≫
        Q.counitIso.hom.app (S.inverse.obj (R.inverse.obj F)) := by
  simp

/-- The pre-coordinate point-span counit splits at the preceding transport
from the actual cover span to the fixed coordinate span. -/
theorem genericPointWedgePreCoordinatePointCounit_eq_preCoordinateSpan_coordinateSpan :
    let C := genericPointWedgeTarget x₀ y₀
    let A := genericPointWedgePreCoordinateSpanMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let B := genericPointWedgeCoordinateSpanEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    let S := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    let Z := Q.inverse.obj (S.inverse.obj (R.inverse.obj F))
    ((A.trans B).counitIso.hom.app Z) =
      B.functor.map (A.counitIso.hom.app (B.inverse.obj Z)) ≫
        B.counitIso.hom.app Z := by
  simp

/-- Projecting the preceding counit split exposes the coordinate-span counit
separately on both transported cover legs. -/
theorem genericPointWedgePreCoordinatePointCounit_legs_eq_preCoordinateSpan_coordinateSpan :
    let C := genericPointWedgeTarget x₀ y₀
    let A := genericPointWedgePreCoordinateSpanMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let B := genericPointWedgeCoordinateSpanEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    let S := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    let Z := Q.inverse.obj (S.inverse.obj (R.inverse.obj F))
    (((A.trans B).counitIso.hom.app Z).left =
        (B.functor.map (A.counitIso.hom.app (B.inverse.obj Z))).left ≫
          (B.counitIso.hom.app Z).left) ∧
      (((A.trans B).counitIso.hom.app Z).right =
        (B.functor.map (A.counitIso.hom.app (B.inverse.obj Z))).right ≫
          (B.counitIso.hom.app Z).right) := by
  constructor
  · exact congrArg (fun k => k.left)
      (genericPointWedgePreCoordinatePointCounit_eq_preCoordinateSpan_coordinateSpan
        x₀ y₀ M N hM hN hy hx cM cN)
  · exact congrArg (fun k => k.right)
      (genericPointWedgePreCoordinatePointCounit_eq_preCoordinateSpan_coordinateSpan
        x₀ y₀ M N hM hN hy hx cM cN)

/-- At the identity point-span object, the remaining coordinate-to-point
counit is exactly the generic span-transport counit. -/
theorem genericPointWedgeCoordinatePointCounit_eq_transportCounit :
    let C := SingleObj (genericPointWedgeFreeProduct x₀ y₀)
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    (genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C).counitIso.hom.app Q =
      counitHom
        (genericPointWedgeCoordinateLeft x₀)
        (genericPointWedgeCoordinateRight y₀)
        (pointLeg (genericPointWedgeLeftGroup x₀))
        (pointLeg (genericPointWedgeRightGroup y₀))
        genericPointWedgeUnitSingleObjEquivalence
        (genericPointWedgeSingleObjEquivalence x₀)
        (genericPointWedgeSingleObjEquivalence y₀)
        (genericPointWedgeCoordinateLeftPointIso x₀)
        (genericPointWedgeCoordinateRightPointIso y₀) Q := by
  rfl

/-- The two legs of the coordinate-to-point counit are precisely the
single-object equivalence counits on the identity point-span legs. -/
theorem genericPointWedgeCoordinatePointCounit_legs :
    let C := SingleObj (genericPointWedgeFreeProduct x₀ y₀)
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let E := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    (E.counitIso.hom.app Q).left =
        ((genericPointWedgeSingleObjEquivalence x₀).congrLeft).counitIso.hom.app Q.left ∧
      (E.counitIso.hom.app Q).right =
        ((genericPointWedgeSingleObjEquivalence y₀).congrLeft).counitIso.hom.app Q.right := by
  exact ⟨rfl, rfl⟩

/-- Evaluating the two coordinate-to-point counit legs at their unique source
objects gives the identity point-span maps of the underlying based counits. -/
theorem genericPointWedgeCoordinatePointCounit_uniqueObjects :
    let C := SingleObj (genericPointWedgeFreeProduct x₀ y₀)
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let E := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    ((E.counitIso.hom.app Q).left).app
          (SingleObj.star (genericPointWedgeLeftGroup x₀)) =
        Q.left.map ((genericPointWedgeSingleObjEquivalence x₀).counit.app
          (SingleObj.star (genericPointWedgeLeftGroup x₀))) ∧
      ((E.counitIso.hom.app Q).right).app
          (SingleObj.star (genericPointWedgeRightGroup y₀)) =
        Q.right.map ((genericPointWedgeSingleObjEquivalence y₀).counit.app
          (SingleObj.star (genericPointWedgeRightGroup y₀))) := by
  exact ⟨rfl, rfl⟩

/-- The based counit element chosen by the left connector equivalence. -/
def genericPointWedgeLeftBasedCounit : genericPointWedgeLeftGroup x₀ :=
  (genericPointWedgeSingleObjEquivalence x₀).counit.app
    (SingleObj.star (genericPointWedgeLeftGroup x₀))

/-- The based counit element chosen by the right connector equivalence. -/
def genericPointWedgeRightBasedCounit : genericPointWedgeRightGroup y₀ :=
  (genericPointWedgeSingleObjEquivalence y₀).counit.app
    (SingleObj.star (genericPointWedgeRightGroup y₀))

/-- The coordinate-to-point counit contributes the coproduct injections of
the two actual based counit elements; no identity normalization is assumed. -/
theorem genericPointWedgeCoordinatePointCounit_uniqueObjects_eq_injections :
    let C := SingleObj (genericPointWedgeFreeProduct x₀ y₀)
    let Q := genericPointWedgeIdentityPointSpan x₀ y₀
    let E := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    ((E.counitIso.hom.app Q).left).app
          (SingleObj.star (genericPointWedgeLeftGroup x₀)) =
        Monoid.Coprod.inl (genericPointWedgeLeftBasedCounit x₀) ∧
      ((E.counitIso.hom.app Q).right).app
          (SingleObj.star (genericPointWedgeRightGroup y₀)) =
        Monoid.Coprod.inr (genericPointWedgeRightBasedCounit y₀) := by
  simp only
  rw [(genericPointWedgeCoordinatePointCounit_uniqueObjects x₀ y₀).1,
    (genericPointWedgeCoordinatePointCounit_uniqueObjects x₀ y₀).2]
  exact ⟨genericPointWedgeIdentityPointSpan_left x₀ y₀ _,
    genericPointWedgeIdentityPointSpan_right x₀ y₀ _⟩

/-- On the left leg, the pre-free-product counit is the mapped
pre-coordinate counit followed by the coordinate-to-point counit. -/
theorem genericPointWedgePreFreeProductCounit_left_eq_preCoordinate_coordinatePoint :
    let C := genericPointWedgeTarget x₀ y₀
    let P := genericPointWedgePreCoordinatePointSpanMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    let S := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    let Z := S.inverse.obj (R.inverse.obj F)
    ((P.trans Q).counitIso.hom.app Z).left =
      (Q.functor.map (P.counitIso.hom.app (Q.inverse.obj Z))).left ≫
        (Q.counitIso.hom.app Z).left := by
  exact congrArg
    (fun k => k.left)
    (genericPointWedgePreFreeProductCounit_eq_preCoordinate_coordinatePoint
      x₀ y₀ M N hM hN hy hx cM cN)

/-- On the right leg, the pre-free-product counit is the mapped
pre-coordinate counit followed by the coordinate-to-point counit. -/
theorem genericPointWedgePreFreeProductCounit_right_eq_preCoordinate_coordinatePoint :
    let C := genericPointWedgeTarget x₀ y₀
    let P := genericPointWedgePreCoordinatePointSpanMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    let S := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    let Z := S.inverse.obj (R.inverse.obj F)
    ((P.trans Q).counitIso.hom.app Z).right =
      (Q.functor.map (P.counitIso.hom.app (Q.inverse.obj Z))).right ≫
        (Q.counitIso.hom.app Z).right := by
  exact congrArg
    (fun k => k.right)
    (genericPointWedgePreFreeProductCounit_eq_preCoordinate_coordinatePoint
      x₀ y₀ M N hM hN hy hx cM cN)

/-- At the left base object, the final factor in the pre-free-product counit
is the coproduct injection of the actual left based connector counit. -/
theorem genericPointWedgePreFreeProductCounit_left_app_eq_preCoordinate_injection :
    let C := genericPointWedgeTarget x₀ y₀
    let P := genericPointWedgePreCoordinatePointSpanMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    let S := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    let Z := S.inverse.obj (R.inverse.obj F)
    (((P.trans Q).counitIso.hom.app Z).left).app
        (SingleObj.star (genericPointWedgeLeftGroup x₀)) =
      ((Q.functor.map (P.counitIso.hom.app (Q.inverse.obj Z))).left).app
          (SingleObj.star (genericPointWedgeLeftGroup x₀)) ≫
        Monoid.Coprod.inl (genericPointWedgeLeftBasedCounit x₀) := by
  dsimp only
  rw [genericPointWedgePreFreeProductCounit_left_eq_preCoordinate_coordinatePoint]
  simp only [NatTrans.comp_app]
  congr 1

/-- At the right base object, the final factor in the pre-free-product counit
is the coproduct injection of the actual right based connector counit. -/
theorem genericPointWedgePreFreeProductCounit_right_app_eq_preCoordinate_injection :
    let C := genericPointWedgeTarget x₀ y₀
    let P := genericPointWedgePreCoordinatePointSpanMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    let S := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    let Z := S.inverse.obj (R.inverse.obj F)
    (((P.trans Q).counitIso.hom.app Z).right).app
        (SingleObj.star (genericPointWedgeRightGroup y₀)) =
      ((Q.functor.map (P.counitIso.hom.app (Q.inverse.obj Z))).right).app
          (SingleObj.star (genericPointWedgeRightGroup y₀)) ≫
        Monoid.Coprod.inr (genericPointWedgeRightBasedCounit y₀) := by
  dsimp only
  rw [genericPointWedgePreFreeProductCounit_right_eq_preCoordinate_coordinatePoint]
  simp only [NatTrans.comp_app]
  congr 1

/-- The left mapped pre-coordinate counit element, isolated before comparison
with the outer span-transport factors. -/
def genericPointWedgeMappedPreCoordinateLeftCounit :
    genericPointWedgeFreeProduct x₀ y₀ :=
  let C := genericPointWedgeTarget x₀ y₀
  let P := genericPointWedgePreCoordinatePointSpanMappingEquivalence
    x₀ y₀ M N hM hN hy hx cM cN C
  let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
  let S := freeProductPointSpanEquivalence
    (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
  let R := representationSingleObjEquivalence
    (C := C) (genericPointWedgeLeftGroup x₀)
      (genericPointWedgeRightGroup y₀)
  let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
  let Z := S.inverse.obj (R.inverse.obj F)
  ((Q.functor.map (P.counitIso.hom.app (Q.inverse.obj Z))).left).app
    (SingleObj.star (genericPointWedgeLeftGroup x₀))

/-- The right mapped pre-coordinate counit element, isolated before comparison
with the outer span-transport factors. -/
def genericPointWedgeMappedPreCoordinateRightCounit :
    genericPointWedgeFreeProduct x₀ y₀ :=
  let C := genericPointWedgeTarget x₀ y₀
  let P := genericPointWedgePreCoordinatePointSpanMappingEquivalence
    x₀ y₀ M N hM hN hy hx cM cN C
  let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
  let S := freeProductPointSpanEquivalence
    (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
  let R := representationSingleObjEquivalence
    (C := C) (genericPointWedgeLeftGroup x₀)
      (genericPointWedgeRightGroup y₀)
  let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
  let Z := S.inverse.obj (R.inverse.obj F)
  ((Q.functor.map (P.counitIso.hom.app (Q.inverse.obj Z))).right).app
    (SingleObj.star (genericPointWedgeRightGroup y₀))

/-- Both evaluated pre-free-product counit legs now have a named first factor;
the remaining comparison is exactly between these elements and the earlier
outer span-transport factors. -/
theorem genericPointWedgePreFreeProductCounit_apps_eq_mappedPreCoordinate_injections :
    let C := genericPointWedgeTarget x₀ y₀
    let P := genericPointWedgePreCoordinatePointSpanMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let Q := genericPointWedgeCoordinatePointSpanEquivalence x₀ y₀ C
    let S := freeProductPointSpanEquivalence
      (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀) C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    let Z := S.inverse.obj (R.inverse.obj F)
    (((P.trans Q).counitIso.hom.app Z).left).app
          (SingleObj.star (genericPointWedgeLeftGroup x₀)) =
        Monoid.Coprod.inl (genericPointWedgeLeftBasedCounit x₀) *
          genericPointWedgeMappedPreCoordinateLeftCounit
            x₀ y₀ M N hM hN hy hx cM cN ∧
      (((P.trans Q).counitIso.hom.app Z).right).app
          (SingleObj.star (genericPointWedgeRightGroup y₀)) =
        Monoid.Coprod.inr (genericPointWedgeRightBasedCounit y₀) *
          genericPointWedgeMappedPreCoordinateRightCounit
            x₀ y₀ M N hM hN hy hx cM cN := by
  constructor
  · simpa [genericPointWedgeMappedPreCoordinateLeftCounit,
      SingleObj.comp_as_mul] using
      (genericPointWedgePreFreeProductCounit_left_app_eq_preCoordinate_injection
        x₀ y₀ M N hM hN hy hx cM cN)
  · simpa [genericPointWedgeMappedPreCoordinateRightCounit,
      SingleObj.comp_as_mul] using
      (genericPointWedgePreFreeProductCounit_right_app_eq_preCoordinate_injection
        x₀ y₀ M N hM hN hy hx cM cN)

/-- Consequently the full B3 counit element is just the mapped counit of the
preceding free-product-representation equivalence. -/
theorem genericPointWedgeCounitElement_eq_mappedRepresentationCounit :
    let C := genericPointWedgeTarget x₀ y₀
    let E := genericPointWedgeFreeProductMappingEquivalence
      x₀ y₀ M N hM hN hy hx cM cN C
    let R := representationSingleObjEquivalence
      (C := C) (genericPointWedgeLeftGroup x₀)
        (genericPointWedgeRightGroup y₀)
    let F := Functor.id (SingleObj (genericPointWedgeFreeProduct x₀ y₀))
    genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN =
      (R.functor.map (E.counitIso.hom.app (R.inverse.obj F))).app
        (SingleObj.star (genericPointWedgeFreeProduct x₀ y₀)) := by
  rw [genericPointWedgeCounitElement_eq_representationCounits,
    genericPointWedgeRepresentationCounit_app_eq_one]
  simp only [SingleObj.comp_as_mul, one_mul]

def genericPointWedgeMappedLeft (g : FundamentalGroup X x₀) :
    genericPointWedgeFreeProduct x₀ y₀ :=
  ((genericPointWedgeSingleObjMappingEquivalence
    x₀ y₀ M N hM hN hy hx cM cN
    (genericPointWedgeTarget x₀ y₀)).functor.obj
      (genericPointWedgeSourceEquivalence
        x₀ y₀ M N hM hN hy hx cM cN).functor).map
          (X := SingleObj.star (genericPointWedgeFreeProduct x₀ y₀))
          (Y := SingleObj.star (genericPointWedgeFreeProduct x₀ y₀))
          (Monoid.Coprod.inl g)

def genericPointWedgeMappedRight (g : FundamentalGroup Y y₀) :
    genericPointWedgeFreeProduct x₀ y₀ :=
  ((genericPointWedgeSingleObjMappingEquivalence
    x₀ y₀ M N hM hN hy hx cM cN
    (genericPointWedgeTarget x₀ y₀)).functor.obj
      (genericPointWedgeSourceEquivalence
        x₀ y₀ M N hM hN hy hx cM cN).functor).map
          (X := SingleObj.star (genericPointWedgeFreeProduct x₀ y₀))
          (Y := SingleObj.star (genericPointWedgeFreeProduct x₀ y₀))
          (Monoid.Coprod.inr g)

theorem genericPointWedgeMappedLeft_eq_conj (g : FundamentalGroup X x₀) :
    genericPointWedgeMappedLeft x₀ y₀ M N hM hN hy hx cM cN g =
      (genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN)⁻¹ *
        Monoid.Coprod.inl g *
          genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN := by
  have h := genericPointWedgeSourceCounit_left
    x₀ y₀ M N hM hN hy hx cM cN g
  change genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN *
      genericPointWedgeMappedLeft x₀ y₀ M N hM hN hy hx cM cN g =
    Monoid.Coprod.inl g *
      genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN at h
  apply mul_left_cancel (a :=
    genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN)
  rw [h]
  simp [mul_assoc]

theorem genericPointWedgeMappedRight_eq_conj (g : FundamentalGroup Y y₀) :
    genericPointWedgeMappedRight x₀ y₀ M N hM hN hy hx cM cN g =
      (genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN)⁻¹ *
        Monoid.Coprod.inr g *
          genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN := by
  have h := genericPointWedgeSourceCounit_right
    x₀ y₀ M N hM hN hy hx cM cN g
  change genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN *
      genericPointWedgeMappedRight x₀ y₀ M N hM hN hy hx cM cN g =
    Monoid.Coprod.inr g *
      genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN at h
  apply mul_left_cancel (a :=
    genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN)
  rw [h]
  simp [mul_assoc]

/-- Inner normalization by the counit element.  Composing the reconstructed
source functor with this automorphism removes exactly the conjugation exposed
by the two preceding theorems. -/
def genericPointWedgeCounitNormalization :
    genericPointWedgeFreeProduct x₀ y₀ ≃*
      genericPointWedgeFreeProduct x₀ y₀ :=
  MulAut.conj
    (genericPointWedgeCounitElement x₀ y₀ M N hM hN hy hx cM cN)

theorem genericPointWedgeCounitNormalization_left
    (g : FundamentalGroup X x₀) :
    genericPointWedgeCounitNormalization x₀ y₀ M N hM hN hy hx cM cN
        (genericPointWedgeMappedLeft x₀ y₀ M N hM hN hy hx cM cN g) =
      Monoid.Coprod.inl g := by
  rw [genericPointWedgeMappedLeft_eq_conj]
  simp [genericPointWedgeCounitNormalization, MulAut.conj_apply, mul_assoc]

theorem genericPointWedgeCounitNormalization_right
    (g : FundamentalGroup Y y₀) :
    genericPointWedgeCounitNormalization x₀ y₀ M N hM hN hy hx cM cN
        (genericPointWedgeMappedRight x₀ y₀ M N hM hN hy hx cM cN g) =
      Monoid.Coprod.inr g := by
  rw [genericPointWedgeMappedRight_eq_conj]
  simp [genericPointWedgeCounitNormalization, MulAut.conj_apply, mul_assoc]

/-- The B4 source equivalence with its target coordinate normalized by the
counit element.  This changes only the chosen free-product coordinate; the
source groupoid and its topological maps are unchanged. -/
def genericPointWedgeNormalizedSourceEquivalence :
    FundamentalGroupoid (Wedge x₀ y₀) ≌
      SingleObj (genericPointWedgeFreeProduct x₀ y₀) :=
  (genericPointWedgeSourceEquivalence
    x₀ y₀ M N hM hN hy hx cM cN).trans
      (genericPointWedgeCounitNormalization
        x₀ y₀ M N hM hN hy hx cM cN).toSingleObjEquiv

/-- The corresponding based equivalence is the old B5 coordinate followed
by the same normalization. -/
def genericPointWedgeNormalizedFundamentalGroupEquiv :
    FundamentalGroup (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀)) ≃*
      genericPointWedgeFreeProduct x₀ y₀ :=
  (genericPointWedgeFundamentalGroupEquiv
    x₀ y₀ M N hM hN hy hx cM cN).trans
      (genericPointWedgeCounitNormalization
        x₀ y₀ M N hM hN hy hx cM cN)

/-- The literal left wedge inclusion on based fundamental groups. -/
def genericPointWedgeLeftLegMap (g : FundamentalGroup X x₀) :
    FundamentalGroup (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀)) :=
  FundamentalGroup.map (includeLeft (x₀ := x₀) (y₀ := y₀)) x₀ g

/-- The literal right wedge inclusion, with the quotient equality changing
its right-hand basepoint representative to the chosen left representative. -/
def genericPointWedgeRightLegMap (g : FundamentalGroup Y y₀) :
    FundamentalGroup (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀)) :=
  FundamentalGroup.mapOfEq
    ⟨fun y => quotientMap x₀ y₀ (.inr y),
      (continuous_quotientMap x₀ y₀).comp continuous_inr⟩
    (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm g

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- Including the lifted left loop from the cover member back into the wedge
recovers the literal left-leg map. -/
theorem genericPointWedgeLeftLiftedLoop_coverInclusion
    (g : FundamentalGroup X x₀) :
    FundamentalGroup.map
        (TwoOpenDescentRestriction.coverPieceInclusion
          (U := genericLeftOpen x₀ y₀ M)
          (V := genericRightOpen x₀ y₀ N) true)
        (genericPointWedgeLeftBase x₀ y₀ M).as
        (genericPointWedgeLeftLiftedLoop x₀ y₀ M g) =
      genericPointWedgeLeftLegMap x₀ y₀ g := by
  rcases g with ⟨p⟩
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- Including the lifted right loop from the cover member back into the wedge
recovers the literal right-leg map, including its quotient basepoint change. -/
theorem genericPointWedgeRightLiftedLoop_coverInclusion
    (g : FundamentalGroup Y y₀) :
    FundamentalGroup.map
        (TwoOpenDescentRestriction.coverPieceInclusion
          (U := genericLeftOpen x₀ y₀ M)
          (V := genericRightOpen x₀ y₀ N) false)
        (genericPointWedgeRightBase x₀ y₀ N).as
        (genericPointWedgeRightLiftedLoop x₀ y₀ N g) =
      genericPointWedgeRightLegMap x₀ y₀ g := by
  rcases g with ⟨p⟩
  change
    (FundamentalGroup.map _ _)
        (FundamentalGroup.mapOfEq _ _ (FundamentalGroup.fromPath (.mk p))) =
      FundamentalGroup.mapOfEq _ _ (FundamentalGroup.fromPath (.mk p))
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  rfl

/-- The B3 inverse-identity functor on the literal left leg is the actual-span
left action on the lifted cover loop. -/
theorem genericPointWedgeInverseIdentity_leftLeg_eq_actualLifted
    (g : FundamentalGroup X x₀) :
    (genericPointWedgeInverseIdentityFunctor
        x₀ y₀ M N hM hN hy hx cM cN).map
          (genericPointWedgeLeftLegMap x₀ y₀ g) =
      (genericPointWedgeIdentityActualSpan
        x₀ y₀ M N hM hN hy hx cM cN).left.map
          (genericPointWedgeLeftLiftedLoop x₀ y₀ M g) := by
  rw [← genericPointWedgeLeftLiftedLoop_coverInclusion]
  rw [genericPointWedgeInverseIdentityFunctor_eq_global]
  exact genericPointWedgeIdentityGlobalLeftBase_map
    x₀ y₀ M N hM hN hy hx cM cN
      (genericPointWedgeLeftLiftedLoop x₀ y₀ M g)

/-- The B3 inverse-identity functor on the literal right leg is the
right-restriction conjugate of the actual-span action on its lifted loop. -/
theorem genericPointWedgeInverseIdentity_rightLeg_eq_actualLifted
    (g : FundamentalGroup Y y₀) :
    (genericPointWedgeInverseIdentityFunctor
        x₀ y₀ M N hM hN hy hx cM cN).map
          (genericPointWedgeRightLegMap x₀ y₀ g) =
      (genericPointWedgeIdentityGlobalRightBaseElement
          x₀ y₀ M N hM hN hy hx cM cN)⁻¹ *
        (genericPointWedgeIdentityActualSpan
          x₀ y₀ M N hM hN hy hx cM cN).right.map
            (genericPointWedgeRightLiftedLoop x₀ y₀ N g) *
        genericPointWedgeIdentityGlobalRightBaseElement
          x₀ y₀ M N hM hN hy hx cM cN := by
  rw [← genericPointWedgeRightLiftedLoop_coverInclusion]
  rw [genericPointWedgeInverseIdentityFunctor_eq_global]
  exact genericPointWedgeIdentityGlobalRightBase_map
    x₀ y₀ M N hM hN hy hx cM cN
      (genericPointWedgeRightLiftedLoop x₀ y₀ N g)

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The left cover equivalence followed by the literal left-leg lift is the
identity continuous map.  Morphism comparison additionally needs transport
across the induced equality of base objects. -/
theorem genericPointWedgeLeftEquiv_comp_leftLegLift :
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun.comp
        (genericPointWedgeLeftLegLift x₀ y₀ M) =
      ContinuousMap.id X := by
  ext x
  exact (genericPointWedgePackage
    x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The right cover equivalence followed by the literal right-leg lift is the
identity continuous map.  Its induced morphism comparison still retains the
quotient base-object transport. -/
theorem genericPointWedgeRightEquiv_comp_rightLegLift :
    (genericPointWedgePackage x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun.comp
        (genericPointWedgeRightLegLift x₀ y₀ N) =
      ContinuousMap.id Y := by
  ext y
  exact (genericPointWedgePackage
    x₀ y₀ M N hM hN hy hx cM cN).right_inclusion y

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The left cover equivalence sends the fixed lifted-leg base object to the
literal base object.  This is propositional rather than definitional and is
the transport used by the connector normal-form calculation. -/
theorem genericPointWedgeLeftEquiv_obj_leftBase :
    (genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor.obj
        (genericPointWedgeLeftBase x₀ y₀ M) =
      FundamentalGroupoid.mk x₀ := by
  apply FundamentalGroupoid.ext
  exact (genericPointWedgePackage
    x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀

omit [PathConnectedSpace Y] in
/-- At the transported left-cover base, the chosen based connector is exactly
the isomorphism induced by the named base-object equality. -/
theorem genericPointWedgeLeftEquiv_leftBase_connector :
    genericPointWedgeBasedConnector x₀
        ((genericPointWedgeLeftGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.obj
            (genericPointWedgeLeftBase x₀ y₀ M)) =
      eqToIso (genericPointWedgeLeftEquiv_obj_leftBase
        x₀ y₀ M N hM hN hy hx cM cN).symm := by
  classical
  simp only [genericPointWedgeBasedConnector]
  rw [dif_pos (genericPointWedgeLeftEquiv_obj_leftBase
    x₀ y₀ M N hM hN hy hx cM cN)]

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The right cover equivalence sends the fixed right-cover representative to
the literal right base object, including the quotient representative change. -/
theorem genericPointWedgeRightEquiv_obj_rightBase :
    (genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor.obj
        (genericPointWedgeRightBase x₀ y₀ N) =
      FundamentalGroupoid.mk y₀ := by
  apply FundamentalGroupoid.ext
  have hz : (genericPointWedgeRightBase x₀ y₀ N).as =
      ⟨quotientMap x₀ y₀ (.inr y₀), ⟨.inr y₀, by trivial, rfl⟩⟩ := by
    apply Subtype.ext
    exact Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)
  change (genericPointWedgePackage
    x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun
      (genericPointWedgeRightBase x₀ y₀ N).as = y₀
  rw [hz]
  exact (genericPointWedgePackage
    x₀ y₀ M N hM hN hy hx cM cN).right_inclusion y₀

omit [PathConnectedSpace X] in
/-- At the transported right-cover base, the chosen based connector is the
isomorphism induced by the named base-object equality. -/
theorem genericPointWedgeRightEquiv_rightBase_connector :
    genericPointWedgeBasedConnector y₀
        ((genericPointWedgeRightGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.obj
            (genericPointWedgeRightBase x₀ y₀ N)) =
      eqToIso (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN).symm := by
  classical
  simp only [genericPointWedgeBasedConnector]
  rw [dif_pos (genericPointWedgeRightEquiv_obj_rightBase
    x₀ y₀ M N hM hN hy hx cM cN)]

omit [PathConnectedSpace X] in
/-- The connector normal form of the mapped lifted right loop is conjugation
by the explicit equality transport at its common endpoint. -/
theorem genericPointWedgeRightLiftedLoop_normalForm_eq_transport
    (g : FundamentalGroup Y y₀) :
    (genericPointWedgeConnectors y₀).normalForm
        ((genericPointWedgeRightGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeRightLiftedLoop x₀ y₀ N g)) =
      eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN).symm ≫
        (genericPointWedgeRightGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeRightLiftedLoop x₀ y₀ N g) ≫
      eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN) := by
  simp only [ConnectorSystem.normalForm, genericPointWedgeConnectors]
  rw [genericPointWedgeRightEquiv_rightBase_connector]
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The functor underlying the right groupoid equivalence is literally the
fundamental-groupoid map of the right cover homotopy equivalence. -/
theorem genericPointWedgeRightGroupoidEquivalence_functor :
    (genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor =
      FundamentalGroupoid.map
        (genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The equivalence map of the lifted right loop is heterogeneously equal to
the concrete fundamental-groupoid map, retaining its dependent endpoints. -/
theorem genericPointWedgeRightLiftedLoop_map_heq
    (g : FundamentalGroup Y y₀) :
    HEq ((genericPointWedgeRightGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeRightLiftedLoop x₀ y₀ N g))
      ((FundamentalGroupoid.map
        (genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun).map
            (genericPointWedgeRightLiftedLoop x₀ y₀ N g)) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- Conjugating the lifted right-loop map by its endpoint transport agrees
with the same conjugation of the concrete induced groupoid map. -/
theorem genericPointWedgeRightLiftedLoop_transport_eq_concrete
    (g : FundamentalGroup Y y₀) :
    eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN).symm ≫
        (genericPointWedgeRightGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeRightLiftedLoop x₀ y₀ N g) ≫
      eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN) =
      eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN).symm ≫
        (FundamentalGroupoid.map
          (genericPointWedgePackage
            x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun).map
              (genericPointWedgeRightLiftedLoop x₀ y₀ N g) ≫
      eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN) := by
  rw [eq_of_heq (genericPointWedgeRightLiftedLoop_map_heq
    x₀ y₀ M N hM hN hy hx cM cN g)]
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The basepoint equality used by the right composite based map is the
pointwise congruence of the composite-map identity. -/
theorem genericPointWedgeRightComposite_baseProof :
    congrArg (fun f : C(Y, Y) => f y₀)
        (genericPointWedgeRightEquiv_comp_rightLegLift
          x₀ y₀ M N hM hN hy hx cM cN) =
      (genericPointWedgePackage
        x₀ y₀ M N hM hN hy hx cM cN).right_inclusion y₀ := by
  apply Subsingleton.elim

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The based map of the right equivalence-lift composite fixes every loop. -/
theorem genericPointWedgeRightComposite_mapOfEq
    (g : FundamentalGroup Y y₀) :
    FundamentalGroup.mapOfEq
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun.comp
            (genericPointWedgeRightLegLift x₀ y₀ N))
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).right_inclusion y₀) g = g := by
  rw [← genericPointWedgeRightComposite_baseProof
    x₀ y₀ M N hM hN hy hx cM cN]
  simp only [genericPointWedgeRightEquiv_comp_rightLegLift]
  have mapOfEq_id (h : (ContinuousMap.id Y) y₀ = y₀) :
      FundamentalGroup.mapOfEq (ContinuousMap.id Y) h g = g := by
    rw [show h = (rfl : y₀ = y₀) by apply Subsingleton.elim]
    rcases g with ⟨p⟩
    simpa [Path.map_id] using
      (FundamentalGroup.mapOfEq_apply
        (f := ContinuousMap.id Y) (h := rfl) p)
  exact mapOfEq_id _

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The right-cover equivalence sends the chosen fixed representative to the
literal base point before passage to the fundamental groupoid. -/
theorem genericPointWedgeRightEquiv_rightBase_as :
    (genericPointWedgePackage
      x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun
        (genericPointWedgeRightBase x₀ y₀ N).as = y₀ := by
  have hz : (genericPointWedgeRightBase x₀ y₀ N).as =
      ⟨quotientMap x₀ y₀ (.inr y₀), ⟨.inr y₀, by trivial, rfl⟩⟩ := by
    apply Subtype.ext
    exact Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)
  rw [hz]
  exact (genericPointWedgePackage
    x₀ y₀ M N hM hN hy hx cM cN).right_inclusion y₀

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The concrete endpoint conjugation is exactly the based map of the right
cover equivalence at the fixed quotient representative. -/
theorem genericPointWedgeRightLiftedLoop_concrete_eq_mapOfEq
    (g : FundamentalGroup Y y₀) :
    eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN).symm ≫
        (FundamentalGroupoid.map
          (genericPointWedgePackage
            x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun).map
              (genericPointWedgeRightLiftedLoop x₀ y₀ N g) ≫
      eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN) =
      FundamentalGroup.mapOfEq
        (genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun
        (genericPointWedgeRightEquiv_rightBase_as
          x₀ y₀ M N hM hN hy hx cM cN)
        (genericPointWedgeRightLiftedLoop x₀ y₀ N g) := by
  rw [show genericPointWedgeRightEquiv_obj_rightBase
      x₀ y₀ M N hM hN hy hx cM cN =
        congrArg FundamentalGroupoid.mk
          (genericPointWedgeRightEquiv_rightBase_as
            x₀ y₀ M N hM hN hy hx cM cN) by
    apply Subsingleton.elim]
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- Applying the right-cover based map to the quotient-adjusted lifted loop
is the based map of the composite, with its literal right-inclusion witness. -/
theorem genericPointWedgeRightLiftedLoop_mapOfEq_comp
    (g : FundamentalGroup Y y₀) :
    FundamentalGroup.mapOfEq
        (genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun
        (genericPointWedgeRightEquiv_rightBase_as
          x₀ y₀ M N hM hN hy hx cM cN)
        (genericPointWedgeRightLiftedLoop x₀ y₀ N g) =
      FundamentalGroup.mapOfEq
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun.comp
            (genericPointWedgeRightLegLift x₀ y₀ N))
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).right_inclusion y₀) g := by
  rcases g with ⟨p⟩
  change FundamentalGroup.mapOfEq _ _
      (FundamentalGroup.mapOfEq _ _
        (FundamentalGroup.fromPath (.mk p))) =
    FundamentalGroup.mapOfEq _ _ (FundamentalGroup.fromPath (.mk p))
  rw [FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply]
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The endpoint-conjugated image of the quotient-adjusted right lifted loop
is the original loop. -/
theorem genericPointWedgeRightLiftedLoop_concrete_eq
    (g : FundamentalGroup Y y₀) :
    eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN).symm ≫
        (FundamentalGroupoid.map
          (genericPointWedgePackage
            x₀ y₀ M N hM hN hy hx cM cN).rightEquiv.toFun).map
              (genericPointWedgeRightLiftedLoop x₀ y₀ N g) ≫
      eqToHom (genericPointWedgeRightEquiv_obj_rightBase
        x₀ y₀ M N hM hN hy hx cM cN) = g := by
  rw [genericPointWedgeRightLiftedLoop_concrete_eq_mapOfEq,
    genericPointWedgeRightLiftedLoop_mapOfEq_comp,
    genericPointWedgeRightComposite_mapOfEq]

omit [PathConnectedSpace X] in
/-- The connector normal form of the mapped lifted right loop is the original
right-summand loop. -/
theorem genericPointWedgeRightLiftedLoop_normalForm
    (g : FundamentalGroup Y y₀) :
    (genericPointWedgeConnectors y₀).normalForm
        ((genericPointWedgeRightGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeRightLiftedLoop x₀ y₀ N g)) = g := by
  rw [genericPointWedgeRightLiftedLoop_normalForm_eq_transport,
    genericPointWedgeRightLiftedLoop_transport_eq_concrete,
    genericPointWedgeRightLiftedLoop_concrete_eq]

omit [PathConnectedSpace Y] in
/-- The connector normal form of the mapped lifted left loop is conjugation
by the explicit equality transport at its common endpoint. -/
theorem genericPointWedgeLeftLiftedLoop_normalForm_eq_transport
    (g : FundamentalGroup X x₀) :
    (genericPointWedgeConnectors x₀).normalForm
        ((genericPointWedgeLeftGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeLeftLiftedLoop x₀ y₀ M g)) =
      eqToHom (genericPointWedgeLeftEquiv_obj_leftBase
        x₀ y₀ M N hM hN hy hx cM cN).symm ≫
        (genericPointWedgeLeftGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeLeftLiftedLoop x₀ y₀ M g) ≫
      eqToHom (genericPointWedgeLeftEquiv_obj_leftBase
        x₀ y₀ M N hM hN hy hx cM cN) := by
  simp only [ConnectorSystem.normalForm, genericPointWedgeConnectors]
  rw [genericPointWedgeLeftEquiv_leftBase_connector]
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The basepoint equality used by the composite based map is the pointwise
congruence of the composite-map identity. -/
theorem genericPointWedgeLeftComposite_baseProof :
    congrArg (fun f : C(X, X) => f x₀)
        (genericPointWedgeLeftEquiv_comp_leftLegLift
          x₀ y₀ M N hM hN hy hx cM cN) =
      (genericPointWedgePackage
        x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀ := by
  apply Subsingleton.elim

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The based map of the left equivalence-lift composite fixes every loop. -/
theorem genericPointWedgeLeftComposite_mapOfEq
    (g : FundamentalGroup X x₀) :
    FundamentalGroup.mapOfEq
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun.comp
            (genericPointWedgeLeftLegLift x₀ y₀ M))
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀) g = g := by
  rw [← genericPointWedgeLeftComposite_baseProof
    x₀ y₀ M N hM hN hy hx cM cN]
  simp only [genericPointWedgeLeftEquiv_comp_leftLegLift]
  have mapOfEq_id (h : (ContinuousMap.id X) x₀ = x₀) :
      FundamentalGroup.mapOfEq (ContinuousMap.id X) h g = g := by
    rw [show h = (rfl : x₀ = x₀) by apply Subsingleton.elim]
    rcases g with ⟨p⟩
    simpa [Path.map_id] using
      (FundamentalGroup.mapOfEq_apply
        (f := ContinuousMap.id X) (h := rfl) p)
  exact mapOfEq_id _

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The functor underlying the left groupoid equivalence is literally the
fundamental-groupoid map of the cover homotopy equivalence. -/
theorem genericPointWedgeLeftGroupoidEquivalence_functor :
    (genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor =
      FundamentalGroupoid.map
        (genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The equivalence map of the lifted loop is heterogeneously equal to the
concrete fundamental-groupoid map, retaining its dependent endpoints. -/
theorem genericPointWedgeLeftLiftedLoop_map_heq
    (g : FundamentalGroup X x₀) :
    HEq ((genericPointWedgeLeftGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeLeftLiftedLoop x₀ y₀ M g))
      ((FundamentalGroupoid.map
        (genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun).map
            (genericPointWedgeLeftLiftedLoop x₀ y₀ M g)) := by
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- Conjugating the lifted-loop map by its endpoint transport agrees with the
same conjugation of the concrete induced groupoid map. -/
theorem genericPointWedgeLeftLiftedLoop_transport_eq_concrete
    (g : FundamentalGroup X x₀) :
    eqToHom (genericPointWedgeLeftEquiv_obj_leftBase
        x₀ y₀ M N hM hN hy hx cM cN).symm ≫
        (genericPointWedgeLeftGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeLeftLiftedLoop x₀ y₀ M g) ≫
      eqToHom (genericPointWedgeLeftEquiv_obj_leftBase
        x₀ y₀ M N hM hN hy hx cM cN) =
      eqToHom (congrArg FundamentalGroupoid.mk
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀)).symm ≫
        (FundamentalGroupoid.map
          (genericPointWedgePackage
            x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun).map
              (genericPointWedgeLeftLiftedLoop x₀ y₀ M g) ≫
      eqToHom (congrArg FundamentalGroupoid.mk
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀)) := by
  rw [eq_of_heq (genericPointWedgeLeftLiftedLoop_map_heq
    x₀ y₀ M N hM hN hy hx cM cN g)]
  rw [show genericPointWedgeLeftEquiv_obj_leftBase
      x₀ y₀ M N hM hN hy hx cM cN =
        congrArg FundamentalGroupoid.mk
          ((genericPointWedgePackage
            x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀) by
    apply Subsingleton.elim]
  rfl

omit [PathConnectedSpace X] [PathConnectedSpace Y] in
/-- The concrete endpoint-conjugated image of the lifted left loop is the
original loop. -/
theorem genericPointWedgeLeftLiftedLoop_concrete_eq
    (g : FundamentalGroup X x₀) :
    eqToHom (congrArg FundamentalGroupoid.mk
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀)).symm ≫
        (FundamentalGroupoid.map
          (genericPointWedgePackage
            x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun).map
              (genericPointWedgeLeftLiftedLoop x₀ y₀ M g) ≫
      eqToHom (congrArg FundamentalGroupoid.mk
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀)) = g := by
  calc
    _ = FundamentalGroup.mapOfEq
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun.comp
            (genericPointWedgeLeftLegLift x₀ y₀ M))
        ((genericPointWedgePackage
          x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀) g := by
          rcases g with ⟨p⟩
          change FundamentalGroup.mapOfEq
              (genericPointWedgePackage
                x₀ y₀ M N hM hN hy hx cM cN).leftEquiv.toFun
              ((genericPointWedgePackage
                x₀ y₀ M N hM hN hy hx cM cN).left_inclusion x₀)
              (FundamentalGroup.map
                (genericPointWedgeLeftLegLift x₀ y₀ M) x₀
                (FundamentalGroup.fromPath (.mk p))) =
            FundamentalGroup.mapOfEq _ _
              (FundamentalGroup.fromPath (.mk p))
          rw [FundamentalGroup.map_apply,
            ← Path.Homotopic.Quotient.mk_map]
          change FundamentalGroup.mapOfEq _ _
              (FundamentalGroup.fromPath (.mk
                (p.map (genericPointWedgeLeftLegLift
                  x₀ y₀ M).continuous))) = _
          rw [FundamentalGroup.mapOfEq_apply,
            FundamentalGroup.mapOfEq_apply]
          rfl
    _ = g := genericPointWedgeLeftComposite_mapOfEq
      x₀ y₀ M N hM hN hy hx cM cN g

omit [PathConnectedSpace Y] in
/-- The connector normal form of the mapped lifted left loop is the original
left-summand loop. -/
theorem genericPointWedgeLeftLiftedLoop_normalForm
    (g : FundamentalGroup X x₀) :
    (genericPointWedgeConnectors x₀).normalForm
        ((genericPointWedgeLeftGroupoidEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
            (genericPointWedgeLeftLiftedLoop x₀ y₀ M g)) = g := by
  rw [genericPointWedgeLeftLiftedLoop_normalForm_eq_transport,
    genericPointWedgeLeftLiftedLoop_transport_eq_concrete,
    genericPointWedgeLeftLiftedLoop_concrete_eq]

/-- The actual left-cover action on a lifted summand loop is the left
coproduct injection. -/
theorem genericPointWedgeIdentityActualSpan_left_lifted
    (g : FundamentalGroup X x₀) :
    (genericPointWedgeIdentityActualSpan
      x₀ y₀ M N hM hN hy hx cM cN).left.map
        (genericPointWedgeLeftLiftedLoop x₀ y₀ M g) =
      Monoid.Coprod.inl g := by
  rw [genericPointWedgeIdentityActualSpan_left_map]
  rw [eq_of_heq (genericPointWedgeIdentityCoordinateSpan_left_map
    x₀ y₀ ((genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor.map
        (genericPointWedgeLeftLiftedLoop x₀ y₀ M g)))]
  rw [genericPointWedgeLeftLiftedLoop_normalForm]

/-- The actual right-cover action on a lifted summand loop is the right
coproduct injection. -/
theorem genericPointWedgeIdentityActualSpan_right_lifted
    (g : FundamentalGroup Y y₀) :
    (genericPointWedgeIdentityActualSpan
      x₀ y₀ M N hM hN hy hx cM cN).right.map
        (genericPointWedgeRightLiftedLoop x₀ y₀ N g) =
      Monoid.Coprod.inr g := by
  rw [genericPointWedgeIdentityActualSpan_right_map]
  rw [eq_of_heq (genericPointWedgeIdentityCoordinateSpan_right_map
    x₀ y₀ ((genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor.map
        (genericPointWedgeRightLiftedLoop x₀ y₀ N g)))]
  rw [genericPointWedgeRightLiftedLoop_normalForm]

/-- The reconstructed inverse-of-identity functor sends the literal left leg
to the literal left coproduct injection. -/
theorem genericPointWedgeInverseIdentity_leftLeg_eq_inl
    (g : FundamentalGroup X x₀) :
    (genericPointWedgeInverseIdentityFunctor
      x₀ y₀ M N hM hN hy hx cM cN).map
        (genericPointWedgeLeftLegMap x₀ y₀ g) = Monoid.Coprod.inl g := by
  rw [genericPointWedgeInverseIdentity_leftLeg_eq_actualLifted,
    genericPointWedgeIdentityActualSpan_left_lifted]

/-- The reconstructed inverse-of-identity functor sends the literal right leg
to the right injection conjugated by the fixed restriction element. -/
theorem genericPointWedgeInverseIdentity_rightLeg_eq_conj_inr
    (g : FundamentalGroup Y y₀) :
    (genericPointWedgeInverseIdentityFunctor
      x₀ y₀ M N hM hN hy hx cM cN).map
        (genericPointWedgeRightLegMap x₀ y₀ g) =
      (genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN)⁻¹ * Monoid.Coprod.inr g *
      genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN := by
  rw [genericPointWedgeInverseIdentity_rightLeg_eq_actualLifted,
    genericPointWedgeIdentityActualSpan_right_lifted]

/-- The reconstructed B4 source functor is literal on the left injection. -/
theorem genericPointWedgeSourceFunctor_leftLeg_eq_inl
    (g : FundamentalGroup X x₀) :
    (genericPointWedgeSourceEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor.map
        (genericPointWedgeLeftLegMap x₀ y₀ g) = Monoid.Coprod.inl g := by
  rw [genericPointWedgeSourceFunctor_map_eq_inverseIdentity,
    genericPointWedgeInverseIdentity_leftLeg_eq_inl]

/-- The reconstructed B4 source functor has exactly the right restriction
conjugation on the literal right injection. -/
theorem genericPointWedgeSourceFunctor_rightLeg_eq_conj_inr
    (g : FundamentalGroup Y y₀) :
    (genericPointWedgeSourceEquivalence
      x₀ y₀ M N hM hN hy hx cM cN).functor.map
        (genericPointWedgeRightLegMap x₀ y₀ g) =
      (genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN)⁻¹ * Monoid.Coprod.inr g *
      genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ M N hM hN hy hx cM cN := by
  rw [genericPointWedgeSourceFunctor_map_eq_inverseIdentity,
    genericPointWedgeInverseIdentity_rightLeg_eq_conj_inr]

/-- Once B3's two mapped actions are identified with the images of the
literal topological legs under B5, the normalized equivalence has exactly the
two coproduct coordinates required by B6. -/
theorem genericPointWedgeLegCoordinates_of_mapped
    (hleft : ∀ g : FundamentalGroup X x₀,
      genericPointWedgeFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeLeftLegMap x₀ y₀ g) =
        genericPointWedgeMappedLeft x₀ y₀ M N hM hN hy hx cM cN g)
    (hright : ∀ g : FundamentalGroup Y y₀,
      genericPointWedgeFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeRightLegMap x₀ y₀ g) =
        genericPointWedgeMappedRight x₀ y₀ M N hM hN hy hx cM cN g) :
    (∀ g : FundamentalGroup X x₀,
      genericPointWedgeNormalizedFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeLeftLegMap x₀ y₀ g) =
        Monoid.Coprod.inl g) ∧
    (∀ g : FundamentalGroup Y y₀,
      genericPointWedgeNormalizedFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeRightLegMap x₀ y₀ g) =
        Monoid.Coprod.inr g) := by
  constructor
  · intro g
    change genericPointWedgeCounitNormalization
        x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeFundamentalGroupEquiv
            x₀ y₀ M N hM hN hy hx cM cN
              (genericPointWedgeLeftLegMap x₀ y₀ g)) = _
    rw [hleft]
    exact genericPointWedgeCounitNormalization_left
      x₀ y₀ M N hM hN hy hx cM cN g
  · intro g
    change genericPointWedgeCounitNormalization
        x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeFundamentalGroupEquiv
            x₀ y₀ M N hM hN hy hx cM cN
              (genericPointWedgeRightLegMap x₀ y₀ g)) = _
    rw [hright]
    exact genericPointWedgeCounitNormalization_right
      x₀ y₀ M N hM hN hy hx cM cN g

/-- The literal B6 coordinate equations are equivalent to the two remaining
B3 mapped-action comparisons; normalization introduces no further condition. -/
theorem genericPointWedgeLegCoordinates_iff_mapped :
    ((∀ g : FundamentalGroup X x₀,
      genericPointWedgeNormalizedFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeLeftLegMap x₀ y₀ g) =
        Monoid.Coprod.inl g) ∧
     (∀ g : FundamentalGroup Y y₀,
      genericPointWedgeNormalizedFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeRightLegMap x₀ y₀ g) =
        Monoid.Coprod.inr g)) ↔
    ((∀ g : FundamentalGroup X x₀,
      genericPointWedgeFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeLeftLegMap x₀ y₀ g) =
        genericPointWedgeMappedLeft x₀ y₀ M N hM hN hy hx cM cN g) ∧
     (∀ g : FundamentalGroup Y y₀,
      genericPointWedgeFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeRightLegMap x₀ y₀ g) =
        genericPointWedgeMappedRight x₀ y₀ M N hM hN hy hx cM cN g)) := by
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · intro g
      apply (genericPointWedgeCounitNormalization
        x₀ y₀ M N hM hN hy hx cM cN).injective
      rw [genericPointWedgeCounitNormalization_left]
      exact hleft g
    · intro g
      apply (genericPointWedgeCounitNormalization
        x₀ y₀ M N hM hN hy hx cM cN).injective
      rw [genericPointWedgeCounitNormalization_right]
      exact hright g
  · rintro ⟨hleft, hright⟩
    exact genericPointWedgeLegCoordinates_of_mapped
      x₀ y₀ M N hM hN hy hx cM cN hleft hright

/-- Final functor-level form of the B6 residual: the literal coordinates hold
exactly when the reconstructed B4 functor maps the two topological legs to
the two actions computed by B3. -/
theorem genericPointWedgeLegCoordinates_iff_sourceFunctor :
    ((∀ g : FundamentalGroup X x₀,
      genericPointWedgeNormalizedFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeLeftLegMap x₀ y₀ g) =
        Monoid.Coprod.inl g) ∧
     (∀ g : FundamentalGroup Y y₀,
      genericPointWedgeNormalizedFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeRightLegMap x₀ y₀ g) =
        Monoid.Coprod.inr g)) ↔
    ((∀ g : FundamentalGroup X x₀,
      (genericPointWedgeSourceEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
          (genericPointWedgeLeftLegMap x₀ y₀ g) =
        genericPointWedgeMappedLeft x₀ y₀ M N hM hN hy hx cM cN g) ∧
     (∀ g : FundamentalGroup Y y₀,
      (genericPointWedgeSourceEquivalence
          x₀ y₀ M N hM hN hy hx cM cN).functor.map
          (genericPointWedgeRightLegMap x₀ y₀ g) =
        genericPointWedgeMappedRight x₀ y₀ M N hM hN hy hx cM cN g)) := by
  simpa only [genericPointWedgeFundamentalGroupEquiv_apply] using
    genericPointWedgeLegCoordinates_iff_mapped
      x₀ y₀ M N hM hN hy hx cM cN

/-- B6 expressed solely as the action of the explicit B3 inverse object on
the two literal topological legs. -/
theorem genericPointWedgeLegCoordinates_iff_inverseIdentity :
    ((∀ g : FundamentalGroup X x₀,
      genericPointWedgeNormalizedFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeLeftLegMap x₀ y₀ g) =
        Monoid.Coprod.inl g) ∧
     (∀ g : FundamentalGroup Y y₀,
      genericPointWedgeNormalizedFundamentalGroupEquiv
          x₀ y₀ M N hM hN hy hx cM cN
          (genericPointWedgeRightLegMap x₀ y₀ g) =
        Monoid.Coprod.inr g)) ↔
    ((∀ g : FundamentalGroup X x₀,
      (genericPointWedgeInverseIdentityFunctor
          x₀ y₀ M N hM hN hy hx cM cN).map
          (genericPointWedgeLeftLegMap x₀ y₀ g) =
        genericPointWedgeMappedLeft x₀ y₀ M N hM hN hy hx cM cN g) ∧
     (∀ g : FundamentalGroup Y y₀,
      (genericPointWedgeInverseIdentityFunctor
          x₀ y₀ M N hM hN hy hx cM cN).map
          (genericPointWedgeRightLegMap x₀ y₀ g) =
        genericPointWedgeMappedRight x₀ y₀ M N hM hN hy hx cM cN g)) := by
  simpa only [genericPointWedgeSourceFunctor_map_eq_inverseIdentity] using
    genericPointWedgeLegCoordinates_iff_sourceFunctor
      x₀ y₀ M N hM hN hy hx cM cN

end GenericFundamentalGroupEquivalence

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
#print axioms genericPointWedgeCoordinateSpanEquivalence
#print axioms genericPointWedgeCoordinateSpanPostcomposeIso
#print axioms genericPointWedgeCoordinatePointSpanEquivalence
#print axioms genericPointWedgeCoordinatePointSpanPostcomposeIso
#print axioms genericPointWedgeSingleObjMappingEquivalence
#print axioms genericPointWedgePreCoordinatePointSpanMappingEquivalence
#print axioms genericPointWedgePreFreeProductMappingEquivalence
#print axioms genericPointWedgePreFreeProductMappingEquivalence_eq_preCoordinate_trans
#print axioms genericPointWedgeFreeProductMappingEquivalence_eq_pre_trans
#print axioms genericPointWedgeIdentityRepresentation
#print axioms genericPointWedgeIdentityPointSpan
#print axioms genericPointWedgeIdentityCoordinateSpan
#print axioms genericPointWedgeIdentityActualSpan
#print axioms genericPointWedgeIdentityPseudoCocone
#print axioms genericPointWedgeOpenCoverEquivalence
#print axioms genericPointWedgeIdentityGlobalFunctor
#print axioms genericPointWedgeIdentityGlobalLeftRestrictionIso
#print axioms genericPointWedgeIdentityGlobalRightRestrictionIso
#print axioms genericPointWedgeIdentityGlobalLeftRestriction_naturality
#print axioms genericPointWedgeIdentityGlobalRightRestriction_naturality
#print axioms genericPointWedgeIdentityGlobalLeftRestriction_hom_app
#print axioms genericPointWedgeIdentityGlobalLeftRestriction_map
#print axioms genericPointWedgeIdentityGlobalLeftBase_map
#print axioms genericPointWedgeIdentityGlobalRightRestrictionElement
#print axioms genericPointWedgeStrictificationRightBaseElement_eq_glue
#print axioms genericPointWedgeDescentRightBaseElement_eq_one
#print axioms genericPointWedgeIdentityGlobalRightBaseElement_eq_glue
#print axioms genericPointWedgeIdentityGlobalRightBaseElement_eq_actualGlue
#print axioms genericPointWedgeIdentityGlobalRightBaseElement_eq_coordinateReverseGlue
#print axioms genericPointWedgeIdentityGlobalRightBaseElement_eq_outerComparisons
#print axioms genericPointWedgeIdentityCoordinateReverseSpan_glue_app
#print axioms genericPointWedgeIdentityOuterLeftComparison_app
#print axioms genericPointWedgeIdentityOuterRightComparison_app
#print axioms genericPointWedgeIdentityOuterLeftSpanFactor_eq_map
#print axioms genericPointWedgeIdentityOuterRightSpanFactor_eq_map
#print axioms genericPointWedgeIdentityOuterLeftRoundTrip_eq_map
#print axioms genericPointWedgeIdentityOuterRightRoundTrip_eq_map
#print axioms genericPointWedgeIdentityOuterLeftRoundTripComponent_eq_unitMap
#print axioms genericPointWedgeIdentityOuterRightRoundTripComponent_eq_unitInvMap
#print axioms genericPointWedgeIdentityOuterLeftUnit_targetMap_eq_nestedMap
#print axioms genericPointWedgeIdentityOuterRightUnitInv_targetMap_eq_nestedMap
#print axioms genericPointWedgeIdentityOuterLeftUnit_actualMap_eq_inclusionMap
#print axioms genericPointWedgeIdentityOuterRightUnitInv_actualMap_eq_inclusionMap
#print axioms genericPointWedgeIdentityOuterLeftSpanComponent_target
#print axioms genericPointWedgeIdentityOuterLeftSpanComponent_source_eq_nestedObj
#print axioms genericPointWedgeIdentityOuterRightSpanComponent_target
#print axioms genericPointWedgeIdentityOuterRightSpanComponent_source_eq_nestedObj
#print axioms genericPointWedgeIdentityCoordinateWhiskeredGlue_app
#print axioms genericPointWedgeIdentityCoordinateWhiskeredGlue_app_eq_unitBase
#print axioms genericPointWedgeIdentityCoordinateSpan_glue_unitBase
#print axioms genericPointWedgeIdentityPointSpan_whiskeredGlue_eq_one
#print axioms genericPointWedgeIdentityCoordinateSpan_glue_unitBase_eq_comparisons
#print axioms genericPointWedgeIdentityCoordinateLeftComparison_app
#print axioms genericPointWedgeIdentityCoordinateRightComparison_app
#print axioms genericPointWedgeIdentityCoordinateLeftLegFactor_eq_one
#print axioms genericPointWedgeIdentityCoordinateRightLegFactor_eq_one
#print axioms genericPointWedgeIdentityCoordinateLeftRoundTrip_eq_one
#print axioms genericPointWedgeIdentityCoordinateRightRoundTrip_eq_one
#print axioms genericPointWedgeIdentityCoordinateSpan_glue_unitBase_eq_one
#print axioms genericPointWedgeIdentityCoordinateReverseSpan_glue_eq_outerComparisons
#print axioms genericPointWedgeIdentityGlobalRightRestriction_map
#print axioms genericPointWedgeIdentityGlobalRightBase_map
#print axioms genericPointWedgeIdentityRepresentation_inl
#print axioms genericPointWedgeIdentityRepresentation_inr
#print axioms genericPointWedgeIdentityPointSpan_left
#print axioms genericPointWedgeIdentityPointSpan_right
#print axioms genericPointWedgeIdentityCoordinateSpan_left
#print axioms genericPointWedgeIdentityCoordinateSpan_left_map
#print axioms genericPointWedgeIdentityCoordinateSpan_right
#print axioms genericPointWedgeIdentityCoordinateSpan_right_map
#print axioms genericPointWedgeIdentityOuterLeftSpanMap_heq_inl_normalForm
#print axioms genericPointWedgeIdentityOuterRightSpanMap_heq_inr_normalForm
#print axioms genericPointWedgeIdentityOuterLeftSpan_normalForm_eq_connectors
#print axioms genericPointWedgeIdentityOuterRightSpan_normalForm_eq_connectors
#print axioms genericPointWedgeIdentityOuterLeftSpan_targetConnector_heq_refl
#print axioms genericPointWedgeIdentityOuterRightSpan_sourceConnector_heq_refl
#print axioms genericPointWedgeIdentityOuterLeftSpan_sourceConnector_eq_based
#print axioms genericPointWedgeIdentityOuterRightSpan_targetConnector_eq_based
#print axioms genericPointWedgeOverlapToLeft_obj_overlapBase
#print axioms genericPointWedgeOverlapToRight_obj_overlapBase
#print axioms genericPointWedgeLeftLegLift_base
#print axioms genericPointWedgeRightLegLift_base
#print axioms genericPointWedgeLeftLiftedLoop
#print axioms genericPointWedgeRightLiftedLoop
#print axioms genericPointWedgeLeftLiftedLoop_coverInclusion
#print axioms genericPointWedgeRightLiftedLoop_coverInclusion
#print axioms genericPointWedgeInverseIdentity_leftLeg_eq_actualLifted
#print axioms genericPointWedgeInverseIdentity_rightLeg_eq_actualLifted
#print axioms genericPointWedgeLeftEquiv_comp_leftLegLift
#print axioms genericPointWedgeRightEquiv_comp_rightLegLift
#print axioms genericPointWedgeLeftEquiv_obj_leftBase
#print axioms genericPointWedgeLeftEquiv_leftBase_connector
#print axioms genericPointWedgeRightEquiv_obj_rightBase
#print axioms genericPointWedgeRightEquiv_rightBase_connector
#print axioms genericPointWedgeRightLiftedLoop_normalForm_eq_transport
#print axioms genericPointWedgeRightGroupoidEquivalence_functor
#print axioms genericPointWedgeRightLiftedLoop_map_heq
#print axioms genericPointWedgeRightLiftedLoop_transport_eq_concrete
#print axioms genericPointWedgeRightComposite_baseProof
#print axioms genericPointWedgeRightComposite_mapOfEq
#print axioms genericPointWedgeRightEquiv_rightBase_as
#print axioms genericPointWedgeRightLiftedLoop_concrete_eq_mapOfEq
#print axioms genericPointWedgeRightLiftedLoop_mapOfEq_comp
#print axioms genericPointWedgeRightLiftedLoop_concrete_eq
#print axioms genericPointWedgeRightLiftedLoop_normalForm
#print axioms genericPointWedgeLeftLiftedLoop_normalForm_eq_transport
#print axioms genericPointWedgeLeftComposite_baseProof
#print axioms genericPointWedgeLeftComposite_mapOfEq
#print axioms genericPointWedgeLeftGroupoidEquivalence_functor
#print axioms genericPointWedgeLeftLiftedLoop_map_heq
#print axioms genericPointWedgeLeftLiftedLoop_transport_eq_concrete
#print axioms genericPointWedgeLeftLiftedLoop_concrete_eq
#print axioms genericPointWedgeLeftLiftedLoop_normalForm
#print axioms genericPointWedgeIdentityActualSpan_left_lifted
#print axioms genericPointWedgeIdentityActualSpan_right_lifted
#print axioms genericPointWedgeInverseIdentity_leftLeg_eq_inl
#print axioms genericPointWedgeInverseIdentity_rightLeg_eq_conj_inr
#print axioms genericPointWedgeSourceFunctor_leftLeg_eq_inl
#print axioms genericPointWedgeSourceFunctor_rightLeg_eq_conj_inr
#print axioms genericPointWedgeIdentityActualSpan_left_map
#print axioms genericPointWedgeIdentityActualSpan_right_map
#print axioms genericPointWedgeSingleObjPostcomposeIso
#print axioms genericPointWedgeSourceEquivalence
#print axioms genericPointWedgeInverseIdentityFunctor
#print axioms genericPointWedgeInverseIdentityFunctor_eq_global
#print axioms genericPointWedgeSourceFunctor_map_eq_inverseIdentity
#print axioms genericPointWedgeFundamentalGroupEquiv
#print axioms fundamentalGroupMulEquivOfSingleObjEquivalence_apply
#print axioms genericPointWedgeFundamentalGroupEquiv_apply
#print axioms genericPointWedgeSourceCounit_naturality
#print axioms genericPointWedgeSourceCounit_left
#print axioms genericPointWedgeSourceCounit_right
#print axioms genericPointWedgeCounitElement_eq_representationCounits
#print axioms genericPointWedgeRepresentationCounit_app_eq_one
#print axioms genericPointWedgePointSpanCounit_hom_eq_id
#print axioms genericPointWedgeFreeProductCounit_eq_pre_pointSpan
#print axioms genericPointWedgePreFreeProductCounit_eq_preCoordinate_coordinatePoint
#print axioms genericPointWedgePreCoordinateSpanMappingEquivalence
#print axioms genericPointWedgePreCoordinatePointSpanMappingEquivalence_eq_preCoordinateSpan_trans
#print axioms genericPointWedgePreCoordinatePointCounit_eq_preCoordinateSpan_coordinateSpan
#print axioms genericPointWedgePreCoordinatePointCounit_legs_eq_preCoordinateSpan_coordinateSpan
#print axioms genericPointWedgeCoordinatePointCounit_eq_transportCounit
#print axioms genericPointWedgeCoordinatePointCounit_legs
#print axioms genericPointWedgeCoordinatePointCounit_uniqueObjects
#print axioms genericPointWedgeLeftBasedCounit
#print axioms genericPointWedgeRightBasedCounit
#print axioms genericPointWedgeCoordinatePointCounit_uniqueObjects_eq_injections
#print axioms genericPointWedgePreFreeProductCounit_left_eq_preCoordinate_coordinatePoint
#print axioms genericPointWedgePreFreeProductCounit_right_eq_preCoordinate_coordinatePoint
#print axioms genericPointWedgePreFreeProductCounit_left_app_eq_preCoordinate_injection
#print axioms genericPointWedgePreFreeProductCounit_right_app_eq_preCoordinate_injection
#print axioms genericPointWedgeMappedPreCoordinateLeftCounit
#print axioms genericPointWedgeMappedPreCoordinateRightCounit
#print axioms genericPointWedgePreFreeProductCounit_apps_eq_mappedPreCoordinate_injections
#print axioms genericPointWedgeCounitElement_eq_mappedRepresentationCounit
#print axioms genericPointWedgeMappedLeft_eq_conj
#print axioms genericPointWedgeMappedRight_eq_conj
#print axioms genericPointWedgeCounitNormalization_left
#print axioms genericPointWedgeCounitNormalization_right
#print axioms genericPointWedgeNormalizedSourceEquivalence
#print axioms genericPointWedgeNormalizedFundamentalGroupEquiv
#print axioms genericPointWedgeLeftLegMap
#print axioms genericPointWedgeRightLegMap
#print axioms genericPointWedgeLegCoordinates_of_mapped
#print axioms genericPointWedgeLegCoordinates_iff_mapped
#print axioms genericPointWedgeLegCoordinates_iff_sourceFunctor
#print axioms genericPointWedgeLegCoordinates_iff_inverseIdentity

end ConstructionTargets.PointWedgeVanKampen
