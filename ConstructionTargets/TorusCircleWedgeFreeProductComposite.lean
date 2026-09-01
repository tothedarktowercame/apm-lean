import ConstructionTargets.TorusCircleWedgeConnectorComparison
import ConstructionTargets.FreeProductPointSpanRepresentations
import Mathlib.CategoryTheory.CatCommSq

/-!
# Torus-circle wedge pseudococones as free-product representations

This composes the actual-to-coordinate comparison with connector normal forms,
the endpoint group coordinates, and the point-span/free-product equivalence.
The accompanying commuting squares retain target-postcomposition naturality.
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.TorusCircleWedgeFreeProductComposite

open ConstructionTargets.GenericSpanPseudoCoconeTransport
open ConstructionTargets.TorusCircleWedgeFundamentalGroupoidSpan
open ConstructionTargets.TorusCircleWedgeConnectorComparison
open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.ConnectedGroupoidSingleObjEquivalence
open ConstructionTargets.FreeProductPointSpanRepresentations

abbrev GT := Multiplicative (ℤ × ℤ)
abbrev GC := Multiplicative ℤ

abbrev connectorLeft :=
  (inducedVertexHom coordinateLeft unitConnectors torusConnectors rfl).toFunctor

abbrev connectorRight :=
  (inducedVertexHom coordinateRight unitConnectors circleConnectors rfl).toFunctor

/-- Any functor from the trivial single-object group is canonically isomorphic
to the point leg. -/
def trivialSourceFunctorIso (M : Type) [Monoid M]
    (F : Functor (SingleObj PUnit.{1}) (SingleObj M)) : F ≅ pointLeg M :=
  NatIso.ofComponents
    (fun X => eqToIso (Subsingleton.elim (F.obj X) ((pointLeg M).obj X))) (by
    intro X Y f
    cases X
    cases Y
    rw [show f = (𝟙 (SingleObj.star PUnit) :
        (SingleObj.star PUnit) ⟶ (SingleObj.star PUnit)) by
      change (f : PUnit) = PUnit.unit
      let p : PUnit := f
      change p = PUnit.unit
      cases p
      rfl]
    have hF : F.map (𝟙 (SingleObj.star PUnit.{1})) = 𝟙 _ := F.map_id _
    have hP : (pointLeg M).map (𝟙 (SingleObj.star PUnit.{1})) = 𝟙 _ :=
      (pointLeg M).map_id _
    erw [hF, hP]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

def connectorSpanEquivalence (C : Type) [Category C] :=
  pseudoCoconeEquivalenceOfSpanEquivalences
    coordinateLeft coordinateRight connectorLeft connectorRight
    (connectorSingleObjEquivalence unitConnectors)
    (connectorSingleObjEquivalence torusConnectors)
    (connectorSingleObjEquivalence circleConnectors)
    coordinateLeftConnectorComparison coordinateRightConnectorComparison
    (C := C)

def pointLeftComparison :
    unitEndMulEquiv.toSingleObjEquiv.inverse ⋙ connectorLeft ⋙
      torusEndMulEquiv.toSingleObjEquiv.functor ≅ pointLeg GT :=
  trivialSourceFunctorIso GT _

def pointRightComparison :
    unitEndMulEquiv.toSingleObjEquiv.inverse ⋙ connectorRight ⋙
      circleEndMulEquiv.toSingleObjEquiv.functor ≅ pointLeg GC :=
  trivialSourceFunctorIso GC _

def pointSpanEquivalence (C : Type) [Category C] :=
  pseudoCoconeEquivalenceOfSpanEquivalences
    connectorLeft connectorRight (pointLeg GT) (pointLeg GC)
    unitEndMulEquiv.toSingleObjEquiv
    torusEndMulEquiv.toSingleObjEquiv
    circleEndMulEquiv.toSingleObjEquiv
    pointLeftComparison pointRightComparison (C := C)

/-- Coordinate-span pseudococones, with the torus factor first and circle
factor second, represented by the corresponding free-product action. -/
def coordinateToFreeProductEquivalence (C : Type) [Category C] :
    SpanPseudoCocone coordinateLeft coordinateRight C ≌
      FreeProductRepresentation (C := C) GT GC :=
  ((connectorSpanEquivalence C).trans (pointSpanEquivalence C)).trans
    (freeProductPointSpanEquivalence GT GC C)

/-- The full composite from the actual torus-circle wedge span to
free-product representations. -/
def actualToFreeProductEquivalence (C : Type) [Category C] :
    SpanPseudoCocone actualLeft actualRight C ≌
      FreeProductRepresentation (C := C) GT GC :=
  (coordinatePseudoCoconeEquivalence (C := C)).trans
    (coordinateToFreeProductEquivalence C)

variable {C D : Type} [Category C] [Category D]

@[reducible] def connectorSquare (H : Functor C D) : CatCommSq
    (postcomposeFunctor H)
    (connectorSpanEquivalence C).functor
    (connectorSpanEquivalence D).functor
    (postcomposeFunctor H) where
  iso := equivalenceFunctorPostcomposeIso
    coordinateLeft coordinateRight connectorLeft connectorRight
    (connectorSingleObjEquivalence unitConnectors)
    (connectorSingleObjEquivalence torusConnectors)
    (connectorSingleObjEquivalence circleConnectors)
    coordinateLeftConnectorComparison coordinateRightConnectorComparison H

@[reducible] def pointSquare (H : Functor C D) : CatCommSq
    (postcomposeFunctor H)
    (pointSpanEquivalence C).functor
    (pointSpanEquivalence D).functor
    (postcomposeFunctor H) where
  iso := equivalenceFunctorPostcomposeIso
    connectorLeft connectorRight (pointLeg GT) (pointLeg GC)
    unitEndMulEquiv.toSingleObjEquiv
    torusEndMulEquiv.toSingleObjEquiv
    circleEndMulEquiv.toSingleObjEquiv
    pointLeftComparison pointRightComparison H

@[reducible] def freeProductSquare (H : Functor C D) : CatCommSq
    (postcomposeFunctor H)
    (freeProductPointSpanEquivalence GT GC C).functor
    (freeProductPointSpanEquivalence GT GC D).functor
    (postcomposeRepresentationFunctor GT GC H) where
  iso := ConstructionTargets.FreeProductPointSpanRepresentations.equivalenceFunctorPostcomposeIso
    GT GC H

@[reducible] def coordinateFreeProductSquare (H : Functor C D) : CatCommSq
    (postcomposeFunctor H)
    (coordinateToFreeProductEquivalence C).functor
    (coordinateToFreeProductEquivalence D).functor
    (postcomposeRepresentationFunctor GT GC H) :=
  CatCommSq.vComp' (CatCommSq.vComp' (connectorSquare H) (pointSquare H))
    (freeProductSquare H)

def coordinateToFreeProductPostcomposeIso (H : Functor C D) :=
  (coordinateFreeProductSquare H).iso

@[reducible] def actualCoordinateSquare (H : Functor C D) : CatCommSq
    (postcomposeFunctor H)
    (coordinatePseudoCoconeEquivalence (C := C)).functor
    (coordinatePseudoCoconeEquivalence (C := D)).functor
    (postcomposeFunctor H) where
  iso := coordinatePseudoCoconePostcomposeIso H

@[reducible] def actualFreeProductSquare (H : Functor C D) : CatCommSq
    (postcomposeFunctor H)
    (actualToFreeProductEquivalence C).functor
    (actualToFreeProductEquivalence D).functor
    (postcomposeRepresentationFunctor GT GC H) :=
  CatCommSq.vComp' (actualCoordinateSquare H) (coordinateFreeProductSquare H)

def actualToFreeProductPostcomposeIso (H : Functor C D) :=
  (actualFreeProductSquare H).iso

#print axioms coordinateToFreeProductEquivalence
#print axioms coordinateToFreeProductPostcomposeIso
#print axioms actualToFreeProductEquivalence
#print axioms actualToFreeProductPostcomposeIso

end ConstructionTargets.TorusCircleWedgeFreeProductComposite
