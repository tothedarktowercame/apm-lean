import ConstructionTargets.TwiceSpiralConnectorReconstructionComparison

/-!
# Vertex-data round trip through connector reconstruction

Extraction after reconstruction conjugates each base action by the chosen
connector at its base.  This file retains that automorphism and constructs the
resulting comparison with the original vertex data.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralConnectorVertexRoundTrip

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorReconstructionComparison
open ConstructionTargets.TwiceSpiralConnectorVertexData
open ConstructionTargets.TwiceSpiralConnectorVertexExtraction
open ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d) (C : Type) [Groupoid C]
variable (K : LegCompatibleConnectorSystems B)

abbrev roundTrip (D : VertexData B C K) : VertexData B C K :=
  ((reconstructionFunctor B C K) ⋙ (extractionFunctor B C K)).obj D

abbrev reconstructedCocone (D : VertexData B C K) : CoordinatePseudoCocone h C :=
  (reconstructionFunctor B C K).obj D

/-- The left comparison retains the represented connector at the left base. -/
def leftBaseComparisonIso (D : VertexData B C K) :
    (roundTrip B C K D).leftTarget ≅ D.leftTarget :=
  (reconstructedCocone B C K D).left.mapIso
    (K.toCoordinateConnectorSystems.left.connector
      K.toCoordinateConnectorSystems.left.base)

/-- The right comparison retains the represented connector at the right base. -/
def rightBaseComparisonIso (D : VertexData B C K) :
    (roundTrip B C K D).rightTarget ≅ D.rightTarget :=
  (reconstructedCocone B C K D).right.mapIso
    (K.toCoordinateConnectorSystems.right.connector
      K.toCoordinateConnectorSystems.right.base)

theorem monoidHom_map_comp {A Z : C} (ρ : End A →* End Z)
    (f g : End A) : ρ (f ≫ g) = ρ f ≫ ρ g := by
  change ρ (g * f) = ρ g * ρ f
  exact map_mul ρ g f

theorem monoidHom_conjugation_intertwines {G H : Type} [Group G] [Group H]
    (ρ : G →* H) (c g : G) :
    ρ c * ρ (c⁻¹ * (g * c)) = ρ g * ρ c := by simp

/-- Comparison from extraction-after-reconstruction to the original vertex
data.  Its intertwining equations are connector normal-form reconstruction;
its glue square is the reconstructed pseudococone comparison at the boundary
base. -/
def roundTripHom (D : VertexData B C K) : roundTrip B C K D ⟶ D where
  left := (leftBaseComparisonIso B C K D).hom
  right := (rightBaseComparisonIso B C K D).hom
  left_intertwines g := by
    let c : End K.toCoordinateConnectorSystems.left.base :=
      (K.toCoordinateConnectorSystems.left.connector
        K.toCoordinateConnectorSystems.left.base).hom
    have hc_inv : c⁻¹ = (K.toCoordinateConnectorSystems.left.connector
        K.toCoordinateConnectorSystems.left.base).inv := by
      change Groupoid.inv (K.toCoordinateConnectorSystems.left.connector
        K.toCoordinateConnectorSystems.left.base).hom = _
      rw [Groupoid.inv_eq_inv]
      simp
    change (reconstructedCocone B C K D).left.map g ≫
        (reconstructedCocone B C K D).left.map c =
      (reconstructedCocone B C K D).left.map c ≫ D.leftHom g
    dsimp [reconstructedCocone, reconstructionFunctor,
      LegCompatibleConnectorSystems.coordinatePseudoCocone]
    dsimp [c]
    simpa [ConnectorSystem.normalForm, Category.assoc, End.mul_def, c, hc_inv] using
      (monoidHom_conjugation_intertwines D.leftHom c g)
  right_intertwines g := by
    let c : End K.toCoordinateConnectorSystems.right.base :=
      (K.toCoordinateConnectorSystems.right.connector
        K.toCoordinateConnectorSystems.right.base).hom
    have hc_inv : c⁻¹ = (K.toCoordinateConnectorSystems.right.connector
        K.toCoordinateConnectorSystems.right.base).inv := by
      change Groupoid.inv (K.toCoordinateConnectorSystems.right.connector
        K.toCoordinateConnectorSystems.right.base).hom = _
      rw [Groupoid.inv_eq_inv]
      simp
    change (reconstructedCocone B C K D).right.map g ≫
        (reconstructedCocone B C K D).right.map c =
      (reconstructedCocone B C K D).right.map c ≫ D.rightHom g
    dsimp [reconstructedCocone, reconstructionFunctor,
      LegCompatibleConnectorSystems.coordinatePseudoCocone]
    dsimp [c]
    simpa [ConnectorSystem.normalForm, Category.assoc, End.mul_def, c, hc_inv] using
      (monoidHom_conjugation_intertwines D.rightHom c g)
  baseGlue_square := by
    exact NatTrans.congr_app
      (reconstruction_glue_square B C K (reconstructedCocone B C K D))
      K.toCoordinateConnectorSystems.boundary.base

theorem inverse_intertwines {A A' : C} (e : A ≅ A')
    {G : Type} (ρ : G → (A ⟶ A)) (ρ' : G → (A' ⟶ A'))
    (hs : ∀ g, ρ g ≫ e.hom = e.hom ≫ ρ' g) (g : G) :
    ρ' g ≫ e.inv = e.inv ≫ ρ g :=
  inverse_square C e e (ρ g) (ρ' g) (hs g)

theorem inverse_glue_square {A A' Z Z' : C}
    (l : A ≅ A') (r : Z ≅ Z') (a : A ⟶ Z) (b : A' ⟶ Z')
    (hs : a ≫ r.hom = l.hom ≫ b) : b ≫ r.inv = l.inv ≫ a :=
  inverse_square C l r a b hs

/-- Inverse vertex-data comparison, derived without setting either base
connector to the identity. -/
def roundTripInv (D : VertexData B C K) : D ⟶ roundTrip B C K D where
  left := (leftBaseComparisonIso B C K D).inv
  right := (rightBaseComparisonIso B C K D).inv
  left_intertwines g := inverse_intertwines C (leftBaseComparisonIso B C K D)
    (fun x => (roundTrip B C K D).leftHom x) (fun x => D.leftHom x)
    (roundTripHom B C K D).left_intertwines g
  right_intertwines g := inverse_intertwines C (rightBaseComparisonIso B C K D)
    (fun x => (roundTrip B C K D).rightHom x) (fun x => D.rightHom x)
    (roundTripHom B C K D).right_intertwines g
  baseGlue_square := inverse_glue_square C
    (leftBaseComparisonIso B C K D) (rightBaseComparisonIso B C K D)
    (roundTrip B C K D).baseGlue.hom D.baseGlue.hom
    (roundTripHom B C K D).baseGlue_square

/-- Extraction after reconstruction is objectwise isomorphic to the original
connector-compatible vertex data. -/
def roundTripIso (D : VertexData B C K) : roundTrip B C K D ≅ D where
  hom := roundTripHom B C K D
  inv := roundTripInv B C K D
  hom_inv_id := by
    apply VertexDataHom.ext
    · exact (leftBaseComparisonIso B C K D).hom_inv_id
    · exact (rightBaseComparisonIso B C K D).hom_inv_id
  inv_hom_id := by
    apply VertexDataHom.ext
    · exact (leftBaseComparisonIso B C K D).inv_hom_id
    · exact (rightBaseComparisonIso B C K D).inv_hom_id

/-- The objectwise comparison is natural in vertex-data intertwiners. -/
theorem roundTripIso_naturality {D E : VertexData B C K} (f : D ⟶ E) :
    ((reconstructionFunctor B C K) ⋙ (extractionFunctor B C K)).map f ≫
        (roundTripIso B C K E).hom =
      (roundTripIso B C K D).hom ≫ f := by
  apply VertexDataHom.ext
  · exact ((leftNatTrans B C K f).naturality
      (K.toCoordinateConnectorSystems.left.connector
        K.toCoordinateConnectorSystems.left.base).hom).symm
  · exact ((rightNatTrans B C K f).naturality
      (K.toCoordinateConnectorSystems.right.connector
        K.toCoordinateConnectorSystems.right.base).hom).symm

/-- Natural isomorphism from reconstruction-then-extraction to the identity
functor on connector-compatible vertex data. -/
def roundTripNatIso :
    (reconstructionFunctor B C K) ⋙ (extractionFunctor B C K) ≅
      Functor.id (VertexData B C K) :=
  NatIso.ofComponents (roundTripIso B C K) (by
    intro D E f
    exact roundTripIso_naturality B C K f)

#print axioms roundTripHom
#print axioms roundTripInv
#print axioms roundTripIso
#print axioms roundTripIso_naturality
#print axioms roundTripNatIso

end ConstructionTargets.TwiceSpiralConnectorVertexRoundTrip
