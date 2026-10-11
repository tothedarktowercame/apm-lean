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

def genericPointWedgeSingleObjMappingEquivalence
    (C : Type) [Category C] :
    (FundamentalGroupoid (Wedge x₀ y₀) ⥤ C) ≌
      (SingleObj (genericPointWedgeFreeProduct x₀ y₀) ⥤ C) :=
  (genericPointWedgeFreeProductMappingEquivalence
    x₀ y₀ M N hM hN hy hx cM cN C).trans
      (representationSingleObjEquivalence
        (C := C) (genericPointWedgeLeftGroup x₀) (genericPointWedgeRightGroup y₀))

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
#print axioms genericPointWedgeCoordinateSpanEquivalence
#print axioms genericPointWedgeCoordinateSpanPostcomposeIso
#print axioms genericPointWedgeCoordinatePointSpanEquivalence
#print axioms genericPointWedgeCoordinatePointSpanPostcomposeIso
#print axioms genericPointWedgeSingleObjMappingEquivalence
#print axioms genericPointWedgeSingleObjPostcomposeIso

end ConstructionTargets.PointWedgeVanKampen
