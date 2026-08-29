import ConstructionTargets.TwiceSpiralConnectorReconstructionComparison

/-!
# Naturality of connector reconstruction

The connector comparison from reconstruction-after-extraction to the original
coordinate pseudococone is natural in pseudococone morphisms.  At each piece
object the assertion is precisely naturality of the supplied piece natural
transformation at the chosen, generally nonidentity, connector.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralConnectorReconstructionNaturality

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorReconstructionComparison
open ConstructionTargets.TwiceSpiralConnectorVertexExtraction
open ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d)
variable (C : Type) [Groupoid C]
variable (K : LegCompatibleConnectorSystems B)

/-- Left piece of naturality for the reconstruction comparison.  The equation
is naturality at the chosen connector from the prescribed base to `X`. -/
theorem reconstructionIso_left_naturality
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q)
    (X : FundamentalGroupoid SolidTorus) :
    (((extractionFunctor B C K ⋙ reconstructionFunctor B C K).map τ).left ≫
        (leftReconstructionIso B C K Q).hom).app X =
      ((leftReconstructionIso B C K P).hom ≫ τ.left).app X := by
  change τ.left.app K.toCoordinateConnectorSystems.left.base ≫
      Q.left.map (K.toCoordinateConnectorSystems.left.connector X).hom =
    P.left.map (K.toCoordinateConnectorSystems.left.connector X).hom ≫
      τ.left.app X
  exact (τ.left.naturality
    (K.toCoordinateConnectorSystems.left.connector X).hom).symm

/-- Right piece of naturality for the reconstruction comparison. -/
theorem reconstructionIso_right_naturality
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q)
    (X : FundamentalGroupoid SolidTorus) :
    (((extractionFunctor B C K ⋙ reconstructionFunctor B C K).map τ).right ≫
        (rightReconstructionIso B C K Q).hom).app X =
      ((rightReconstructionIso B C K P).hom ≫ τ.right).app X := by
  change τ.right.app K.toCoordinateConnectorSystems.right.base ≫
      Q.right.map (K.toCoordinateConnectorSystems.right.connector X).hom =
    P.right.map (K.toCoordinateConnectorSystems.right.connector X).hom ≫
      τ.right.app X
  exact (τ.right.naturality
    (K.toCoordinateConnectorSystems.right.connector X).hom).symm

/-- The objectwise connector reconstruction isomorphisms are natural in every
coordinate pseudococone morphism. -/
theorem reconstructionIso_naturality
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q) :
    (extractionFunctor B C K ⋙ reconstructionFunctor B C K).map τ ≫
        (reconstructionIso B C K Q).hom =
      (reconstructionIso B C K P).hom ≫ τ := by
  apply CoordinatePseudoCoconeHom.ext
  · ext X
    exact reconstructionIso_left_naturality B C K τ X
  · ext X
    exact reconstructionIso_right_naturality B C K τ X

/-- Extraction followed by connector reconstruction is naturally isomorphic
to the identity on coordinate pseudococones. -/
def reconstructionNatIso :
    extractionFunctor B C K ⋙ reconstructionFunctor B C K ≅
      𝟭 (CoordinatePseudoCocone h C) :=
  NatIso.ofComponents (reconstructionIso B C K) (by
    intro P Q τ
    exact reconstructionIso_naturality B C K τ)

@[simp] theorem reconstructionNatIso_hom_app
    (Q : CoordinatePseudoCocone h C) :
    (reconstructionNatIso B C K).hom.app Q = reconstructionHom B C K Q := rfl

@[simp] theorem reconstructionNatIso_inv_app
    (Q : CoordinatePseudoCocone h C) :
    (reconstructionNatIso B C K).inv.app Q = reconstructionInv B C K Q := rfl

#print axioms reconstructionIso_left_naturality
#print axioms reconstructionIso_right_naturality
#print axioms reconstructionIso_naturality
#print axioms reconstructionNatIso

end ConstructionTargets.TwiceSpiralConnectorReconstructionNaturality
