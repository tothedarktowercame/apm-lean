import ConstructionTargets.TwoOpenLegCompatibleConnectorSystems
import ConstructionTargets.FreeProductPointSpanRepresentations
noncomputable section
open CategoryTheory
namespace ConstructionTargets.TwoOpenPointSpanComparison
open ConnectedGroupoidSingleObjEquivalence TwoOpenLegCompatibleConnectorSystems
open TwoOpenFundamentalGroupoidSpan GenericSpanPseudoCoconeTransport FreeProductPointSpanRepresentations
variable {X : Type} [TopologicalSpace X] (U V : Set X)
  [PathConnectedSpace U] [PathConnectedSpace V] [SimplyConnectedSpace (U ∩ V : Set X)]
def collapse : FundamentalGroupoid (U ∩ V : Set X) ⥤ SingleObj PUnit.{1} :=
  (Functor.const _).obj (SingleObj.star PUnit.{1})
instance collapse_faithful : (collapse U V).Faithful where
  map_injective := by
    intro a b f g _
    exact @Subsingleton.elim (Path.Homotopic.Quotient a.as b.as) inferInstance f g
instance collapse_full : (collapse U V).Full where
  map_surjective {a b} f := by
    refine ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath a.as b.as), ?_⟩
    exact @Subsingleton.elim PUnit.{1} inferInstance _ _
instance collapse_essSurj : (collapse U V).EssSurj where
  mem_essImage y := by
    let w : (U ∩ V : Set X) := Classical.choice inferInstance
    cases y
    exact ⟨FundamentalGroupoid.mk w, ⟨Iso.refl _⟩⟩
instance collapse_isEquivalence : (collapse U V).IsEquivalence := Functor.IsEquivalence.mk

def overlapEquivalence := (collapse U V).asEquivalence

def pointComparison {G : Type} [Monoid G] (F : SingleObj PUnit.{1} ⥤ SingleObj G) :
    F ≅ pointLeg G :=
  NatIso.ofComponents (fun y => by cases y; exact Iso.refl _) (by
    intro a b f
    cases a; cases b
    have hf : f = 𝟙 (SingleObj.star PUnit.{1}) := @Subsingleton.elim PUnit.{1} inferInstance _ _
    subst f
    change F.map (𝟙 (SingleObj.star PUnit.{1})) ≫ 𝟙 _ = 𝟙 _ ≫ (pointLeg G).map (𝟙 (SingleObj.star PUnit.{1}))
    erw [F.map_id, (pointLeg G).map_id]
    simp
    rfl)

variable (w : (U ∩ V : Set X))
def leftEquivalence := connectorSingleObjEquivalence (leftConnectors w)
def rightEquivalence := connectorSingleObjEquivalence (rightConnectors w)

def leftComparison := pointComparison ((overlapEquivalence U V).inverse ⋙
  overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙ (leftEquivalence U V w).functor)
def rightComparison := pointComparison ((overlapEquivalence U V).inverse ⋙
  overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙ (rightEquivalence U V w).functor)

def comparison (C : Type) [Category C] :=
  pseudoCoconeEquivalenceOfSpanEquivalences
    (overlapFundamentalGroupoidMap (U := U) (V := V) true)
    (overlapFundamentalGroupoidMap (U := U) (V := V) false)
    (pointLeg (End (leftConnectors w).base)) (pointLeg (End (rightConnectors w).base))
    (overlapEquivalence U V) (leftEquivalence U V w) (rightEquivalence U V w)
    (leftComparison U V w) (rightComparison U V w) (C := C)
def postcomposeIso {C D : Type} [Category C] [Category D] (H : C ⥤ D) :
    postcomposeFunctor H ⋙ (comparison U V w D).functor ≅
      (comparison U V w C).functor ⋙ postcomposeFunctor H :=
  equivalenceFunctorPostcomposeIso
    (overlapFundamentalGroupoidMap (U := U) (V := V) true)
    (overlapFundamentalGroupoidMap (U := U) (V := V) false)
    (pointLeg (End (leftConnectors w).base)) (pointLeg (End (rightConnectors w).base))
    (overlapEquivalence U V) (leftEquivalence U V w) (rightEquivalence U V w)
    (leftComparison U V w) (rightComparison U V w) H

def inversePostcomposeIso {C D : Type} [Category C] [Category D] (H : C ⥤ D) :
    postcomposeFunctor H ⋙ (comparison U V w D).inverse ≅
      (comparison U V w C).inverse ⋙ postcomposeFunctor H :=
  equivalenceInversePostcomposeIso
    (overlapFundamentalGroupoidMap (U := U) (V := V) true)
    (overlapFundamentalGroupoidMap (U := U) (V := V) false)
    (pointLeg (End (leftConnectors w).base)) (pointLeg (End (rightConnectors w).base))
    (overlapEquivalence U V) (leftEquivalence U V w) (rightEquivalence U V w)
    (leftComparison U V w) (rightComparison U V w) H
#print axioms postcomposeIso
#print axioms inversePostcomposeIso
#print axioms collapse_isEquivalence
#print axioms pointComparison
#print axioms comparison
end ConstructionTargets.TwoOpenPointSpanComparison
