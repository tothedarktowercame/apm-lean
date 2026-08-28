import ConstructionTargets.TwiceSpiralSignedArrowAlgebra
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.BoundaryTorusH0Cokernel
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.IntegralSingularHomologyComparison

/-!
# Production Mayer--Vietoris coordinates for twice-spiral gluing
-/

noncomputable section

namespace ConstructionTargets.TwiceSpiralGluingHomology

universe u

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralH1Coordinates
open ConstructionTargets.TwiceSpiralSignedArrowAlgebra
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BoundaryTorusH0Cokernel
open ConstructionTargets.SolidTorusHomotopyAndHomology
open ConstructionTargets.T00A01MayerVietorisAdapters
open ConstructionTargets.IntegralSingularHomologyComparison

private abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology k (TopCat.of X)

def solidTorusH0GroupIsoInt : H 0 SolidTorus ≅ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv solidTorusHomotopyEquivCircle 0 ≪≫
    circleH0GroupIsoInt

/-- Degree zero closes independently of the twice-spiral H1 comparison. -/
def gluingH0GroupIsoInt (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    H 0 (Gluing h) ≅ AddCommGrpCat.of ℤ := by
  letI : Nonempty (leftOpen h) :=
    ⟨leftSolidTorusInclusion h (1, 0)⟩
  letI : Nonempty (rightOpen h) :=
    ⟨rightSolidTorusInclusion h (1, 0)⟩
  letI : Nonempty (leftOpen h ∩ rightOpen h : Set (Gluing h)) :=
    ⟨boundaryIntersectionInclusion h (1,
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne 1)⟩
  exact openCoverH0IsoOfCoordinates (leftOpen h) (rightOpen h)
    (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h)
    (singularHomologyIsoOfHomotopyEquiv (intersectionPieceHomotopyEquiv h) 0 ≪≫
      boundaryTorusH0GroupIsoInt)
    (singularHomologyIsoOfHomotopyEquiv (leftPieceHomotopyEquiv h) 0 ≪≫
      solidTorusH0GroupIsoInt)
    (singularHomologyIsoOfHomotopyEquiv (rightPieceHomotopyEquiv h) 0 ≪≫
      solidTorusH0GroupIsoInt)

def gluingH0ModuleIsoInt (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Gluing h))) ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of (Gluing h)) 0
    (ModuleCat.of ℤ ℤ)
    (gluingH0GroupIsoInt h)

/-- Recover the additive equivalence underlying a multiplicative equivalence
between multiplicative presentations. -/
def additiveEquivOfMultiplicativeEquiv {A B : Type u}
    [AddCommGroup A] [AddCommGroup B]
    (e : Multiplicative A ≃* Multiplicative B) : A ≃+ B where
  toFun a := Multiplicative.toAdd (e (Multiplicative.ofAdd a))
  invFun b := Multiplicative.toAdd (e.symm (Multiplicative.ofAdd b))
  left_inv a := congrArg Multiplicative.toAdd (e.symm_apply_apply (Multiplicative.ofAdd a))
  right_inv b := congrArg Multiplicative.toAdd (e.apply_symm_apply (Multiplicative.ofAdd b))
  map_add' a b := congrArg Multiplicative.toAdd (e.map_mul
    (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

def addCommGrpIsoOfMultiplicativeEquiv {A B : Type u}
    [AddCommGroup A] [AddCommGroup B]
    (e : Multiplicative A ≃* Multiplicative B) :
    AddCommGrpCat.of A ≅ AddCommGrpCat.of B :=
  (additiveEquivOfMultiplicativeEquiv e).toAddCommGrpIso

/-- H1 of the production intersection, transported first to the literal
boundary torus and then to the supplied π1-derived coordinate. -/
def intersectionH1Coordinate (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (z₀ : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ)) :
    H 1 (leftOpen h ∩ rightOpen h : Set (Gluing h)) ≅ IntPairGroup :=
  singularHomologyIsoOfHomotopyEquiv (intersectionPieceHomotopyEquiv h) 1 ≪≫
    addCommGrpIsoOfMultiplicativeEquiv (boundaryH1CoordinateFromPi e₁)

/-- H1 of both production cover pieces in the supplied π1-derived
solid-torus coordinates. -/
def piecesH1Coordinate (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (z₀ : BoundaryTorus)
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃*
      Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃*
      Multiplicative ℤ) :
    H 1 (leftOpen h) ⊞ H 1 (rightOpen h) ≅
      AddCommGrpCat.of ℤ ⊞ AddCommGrpCat.of ℤ :=
  biprod.mapIso
    (singularHomologyIsoOfHomotopyEquiv (leftPieceHomotopyEquiv h) 1 ≪≫
      addCommGrpIsoOfMultiplicativeEquiv (solidH1CoordinateFromPi c₁))
    (singularHomologyIsoOfHomotopyEquiv (rightPieceHomotopyEquiv h) 1 ≪≫
      addCommGrpIsoOfMultiplicativeEquiv (solidH1CoordinateFromPi c₂))

/-- The actual production intersection arrow, fully conjugated into the
coordinates dictated by the supplied π1 data. -/
def productionH1CoordinateArrow (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (z₀ : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃*
      Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃*
      Multiplicative ℤ) : IntPairGroup ⟶
      (AddCommGrpCat.of ℤ ⊞ AddCommGrpCat.of ℤ) :=
  (intersectionH1Coordinate h z₀ e₁).inv ≫
    productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫
      (piecesH1Coordinate h z₀ c₁ c₂).hom

/-- The precise remaining comparison: after the canonical biproduct-to-product
normalization, the actual production arrow must agree with the signed arrow
already calculated from Hurewicz naturality. -/
def productionH1ArrowComparisonStatement
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z₀ : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup BoundaryTorus (h z₀) ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃*
      Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃*
      Multiplicative ℤ) : Prop :=
  (productionH1CoordinateArrow h z₀ e₁ c₁ c₂ ≫
      (AddCommGrpCat.biprodIsoProd (AddCommGrpCat.of ℤ)
        (AddCommGrpCat.of ℤ)).hom) =
    twiceSpiralSignedArrow
      (twiceSpiralSecondCoefficient h z₀ e₁ e₂)

theorem productionH1CoordinateArrow_eq_conjugated
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z₀ : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃*
      Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃*
      Multiplicative ℤ) :
    productionH1CoordinateArrow h z₀ e₁ c₁ c₂ =
      (intersectionH1Coordinate h z₀ e₁).inv ≫
        productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫
          (piecesH1Coordinate h z₀ c₁ c₂).hom := rfl

#print axioms additiveEquivOfMultiplicativeEquiv
#print axioms gluingH0GroupIsoInt
#print axioms gluingH0ModuleIsoInt
#print axioms productionH1CoordinateArrow_eq_conjugated

end ConstructionTargets.TwiceSpiralGluingHomology
