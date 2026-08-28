import ConstructionTargets.TwiceSpiralSignedArrowAlgebra
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.BoundaryTorusH0Cokernel
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.HomotopyEquivHomologySquare

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
open ConstructionTargets.HomotopyEquivHomologySquare
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.HomologyBiprodNormalization

private abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (ConstructionTargets.SingularSubdivision.SingularChains
    (TopCat.of X)).homology k

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
      Multiplicative ℤ)
    (_hinc₁ : ∀ p, c₁ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ z₀ p) =
        secondCoordinateHom (e₁ p))
    (_hinc₂ : ∀ p, c₂ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ (h z₀) p) =
        secondCoordinateHom (e₂ p))
    (_h10 : boundaryCoordinateMap h z₀ e₁ e₂
      (Multiplicative.ofAdd (1, 0)) = Multiplicative.ofAdd (1, 2)) : Prop :=
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

theorem intersection_left_homology_square
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (singularHomologyIsoOfHomotopyEquiv
        (intersectionPieceHomotopyEquiv h) 1).inv ≫
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (intersectionToLeftOpen h)) ≫
      (singularHomologyIsoOfHomotopyEquiv
        (leftPieceHomotopyEquiv h) 1).hom =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom ⟨boundaryInclusion, continuous_boundaryInclusion⟩) :=
  conjugated_homologyMap_of_strict_square
    (intersectionPieceHomotopyEquiv h) (leftPieceHomotopyEquiv h)
    (intersectionToLeftOpen h)
    ⟨boundaryInclusion, continuous_boundaryInclusion⟩
    (intersection_left_coordinate_strict h) 1

theorem intersection_right_homology_square
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (singularHomologyIsoOfHomotopyEquiv
        (intersectionPieceHomotopyEquiv h) 1).inv ≫
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (intersectionToRightOpen h)) ≫
      (singularHomologyIsoOfHomotopyEquiv
        (rightPieceHomotopyEquiv h) 1).hom =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom ⟨boundaryInclusion ∘ h,
          continuous_boundaryInclusion.comp h.continuous⟩) :=
  conjugated_homologyMap_of_strict_square
    (intersectionPieceHomotopyEquiv h) (rightPieceHomotopyEquiv h)
    (intersectionToRightOpen h)
    ⟨boundaryInclusion ∘ h,
      continuous_boundaryInclusion.comp h.continuous⟩
    (intersection_right_coordinate_strict h) 1

theorem productionIntersectionArrow_fst_functor
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫ biprod.fst =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (intersectionToLeftOpen h)) := by
  simp only [productionIntersectionArrow, biprod.lift_fst]
  exact (singularHomologyFunctor_map_eq_singularPostcomposition
    (intersectionToLeftOpen h) 1).symm

theorem productionIntersectionArrow_snd_functor
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫ biprod.snd =
      -((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (intersectionToRightOpen h)) := by
  simp only [productionIntersectionArrow, biprod.lift_snd]
  rw [singularHomologyFunctor_map_eq_singularPostcomposition]
  exact congrArg Neg.neg
    (ssetHomologyMap_eq_singularPostcomposition (intersectionToRightOpen h) 1)

theorem productionIntersectionArrow_map_fst_functor
    (h : BoundaryTorus ≃ₜ BoundaryTorus) {A B : AddCommGrpCat}
    (u : (ConstructionTargets.SingularSubdivision.SingularChains (TopCat.of (leftOpen h))).homology 1 ⟶ A)
    (v : (ConstructionTargets.SingularSubdivision.SingularChains (TopCat.of (rightOpen h))).homology 1 ⟶ B) :
    productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫
        (biprod.map u v ≫ biprod.fst) =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (intersectionToLeftOpen h)) ≫ u := by
  rw [biprod.map_fst]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ u)
    (productionIntersectionArrow_fst_functor h)

theorem productionIntersectionArrow_map_snd_functor
    (h : BoundaryTorus ≃ₜ BoundaryTorus) {A B : AddCommGrpCat}
    (u : (ConstructionTargets.SingularSubdivision.SingularChains (TopCat.of (leftOpen h))).homology 1 ⟶ A)
    (v : (ConstructionTargets.SingularSubdivision.SingularChains (TopCat.of (rightOpen h))).homology 1 ⟶ B) :
    productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫
        (biprod.map u v ≫ biprod.snd) =
      (-((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (intersectionToRightOpen h))) ≫ v := by
  rw [biprod.map_snd]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ v) (productionIntersectionArrow_snd_functor h)

theorem productionH1CoordinateArrow_fst
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z₀ : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z₀ ≃* Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃* Multiplicative ℤ) :
    productionH1CoordinateArrow h z₀ e₁ c₁ c₂ ≫ biprod.fst =
      (addCommGrpIsoOfMultiplicativeEquiv (boundaryH1CoordinateFromPi e₁)).inv ≫
        HomologicalComplex.homologyMap (singularPostcomposition
          ⟨boundaryInclusion, continuous_boundaryInclusion⟩) 1 ≫
        (addCommGrpIsoOfMultiplicativeEquiv (solidH1CoordinateFromPi c₁)).hom := by
  simp only [productionH1CoordinateArrow, intersectionH1Coordinate,
    piecesH1Coordinate, Iso.trans_inv, Iso.trans_hom, biprod.mapIso_hom,
    ← Category.assoc]
  slice_lhs 3 5 => rw [productionIntersectionArrow_map_fst_functor]
  have hs := congrArg (fun k ↦
      (addCommGrpIsoOfMultiplicativeEquiv
          (boundaryH1CoordinateFromPi e₁)).inv ≫ k ≫
        (addCommGrpIsoOfMultiplicativeEquiv
          (solidH1CoordinateFromPi c₁)).hom)
    (intersection_left_homology_square h)
  rw [singularHomologyFunctor_map_eq_singularPostcomposition] at hs
  simpa only [Category.assoc] using hs

theorem productionH1CoordinateArrow_snd
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z₀ : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z₀ ≃* Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃* Multiplicative ℤ) :
    productionH1CoordinateArrow h z₀ e₁ c₁ c₂ ≫ biprod.snd =
      -((addCommGrpIsoOfMultiplicativeEquiv (boundaryH1CoordinateFromPi e₁)).inv ≫
        HomologicalComplex.homologyMap (singularPostcomposition ⟨h, h.continuous⟩) 1 ≫
        HomologicalComplex.homologyMap (singularPostcomposition
          ⟨boundaryInclusion, continuous_boundaryInclusion⟩) 1 ≫
        (addCommGrpIsoOfMultiplicativeEquiv (solidH1CoordinateFromPi c₂)).hom) := by
  simp only [productionH1CoordinateArrow, intersectionH1Coordinate,
    piecesH1Coordinate, Iso.trans_inv, Iso.trans_hom, biprod.mapIso_hom,
    ← Category.assoc]
  slice_lhs 3 5 => rw [productionIntersectionArrow_map_snd_functor]
  have hs := congrArg (fun k ↦
      (addCommGrpIsoOfMultiplicativeEquiv
          (boundaryH1CoordinateFromPi e₁)).inv ≫ k ≫
        (addCommGrpIsoOfMultiplicativeEquiv
          (solidH1CoordinateFromPi c₂)).hom)
    (intersection_right_homology_square h)
  rw [singularHomologyFunctor_map_eq_singularPostcomposition
    (intersectionToRightOpen h) 1] at hs
  rw [singularHomologyFunctor_map_eq_singularPostcomposition
    ⟨boundaryInclusion ∘ h,
      continuous_boundaryInclusion.comp h.continuous⟩ 1] at hs
  have hcomp : (⟨boundaryInclusion ∘ h,
      continuous_boundaryInclusion.comp h.continuous⟩ : C(BoundaryTorus, SolidTorus)) =
      (⟨boundaryInclusion, continuous_boundaryInclusion⟩ :
        C(BoundaryTorus, SolidTorus)).comp ⟨h, h.continuous⟩ := rfl
  rw [hcomp] at hs
  rw [← singularPostcomposition_comp] at hs
  rw [HomologicalComplex.homologyMap_comp] at hs
  have hsign := fullyLeftAssociated_comp_neg_comp_comp
    (addCommGrpIsoOfMultiplicativeEquiv
      (boundaryH1CoordinateFromPi e₁)).inv
    (singularHomologyIsoOfHomotopyEquiv
      (intersectionPieceHomotopyEquiv h) 1).inv
    (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (intersectionToRightOpen h)))
    (singularHomologyIsoOfHomotopyEquiv
      (rightPieceHomotopyEquiv h) 1).hom
    (addCommGrpIsoOfMultiplicativeEquiv
      (solidH1CoordinateFromPi c₂)).hom
  simpa only [Category.assoc] using hsign.trans
    (congrArg Neg.neg (by simpa only [Category.assoc] using hs))

/-- The production Mayer--Vietoris intersection arrow has the twice-spiral
coordinate formula once the supplied fundamental-group coordinates satisfy
the two inclusion normalizations and the specified first column for `h`. -/
theorem productionH1ArrowComparison
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z₀ : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup BoundaryTorus (h z₀) ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃*
      Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃*
      Multiplicative ℤ)
    (hinc₁ : ∀ p, c₁ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ z₀ p) =
        secondCoordinateHom (e₁ p))
    (hinc₂ : ∀ p, c₂ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ (h z₀) p) =
        secondCoordinateHom (e₂ p))
    (h10 : boundaryCoordinateMap h z₀ e₁ e₂
      (Multiplicative.ofAdd (1, 0)) = Multiplicative.ofAdd (1, 2)) :
    productionH1ArrowComparisonStatement h z₀ e₁ e₂ c₁ c₂
      hinc₁ hinc₂ h10 := by
  apply AddCommGrpCat.hom_ext
  apply DFunLike.ext _ _
  rintro ⟨a, b⟩
  change _ = twiceSpiralSignedH1Arrow
    (twiceSpiralSecondCoefficient h z₀ e₁ e₂) (a, b)
  have hactual := actual_signed_H1_pair_formula h z₀ e₁ e₂ c₁ c₂
    hinc₁ hinc₂ h10 a b
  apply Prod.ext
  · calc
      _ = (productionH1CoordinateArrow h z₀ e₁ c₁ c₂ ≫ biprod.fst)
          (a, b) := by
        symm
        have hf := AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply
            (AddCommGrpCat.of ℤ) (AddCommGrpCat.of ℤ)
            (((AddCommGrpCat.biprodIsoProd (AddCommGrpCat.of ℤ)
              (AddCommGrpCat.of ℤ)).hom)
              (productionH1CoordinateArrow h z₀ e₁ c₁ c₂ (a, b)))
        rw [Iso.hom_inv_id_apply] at hf
        exact hf
      _ = _ := by
        rw [productionH1CoordinateArrow_fst h z₀ e₁ c₁ c₂]
        rfl
      _ = _ := congrArg Prod.fst hactual
  · calc
      _ = (productionH1CoordinateArrow h z₀ e₁ c₁ c₂ ≫ biprod.snd)
          (a, b) := by
        symm
        have hs := AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply
            (AddCommGrpCat.of ℤ) (AddCommGrpCat.of ℤ)
            (((AddCommGrpCat.biprodIsoProd (AddCommGrpCat.of ℤ)
              (AddCommGrpCat.of ℤ)).hom)
              (productionH1CoordinateArrow h z₀ e₁ c₁ c₂ (a, b)))
        rw [Iso.hom_inv_id_apply] at hs
        exact hs
      _ = _ := by
        rw [productionH1CoordinateArrow_snd h z₀ e₁ c₁ c₂]
        rfl
      _ = _ := congrArg Prod.snd hactual

#print axioms additiveEquivOfMultiplicativeEquiv
#print axioms gluingH0GroupIsoInt
#print axioms gluingH0ModuleIsoInt
#print axioms productionH1CoordinateArrow_eq_conjugated
#print axioms intersection_left_homology_square
#print axioms intersection_right_homology_square
#print axioms productionIntersectionArrow_fst_functor
#print axioms productionIntersectionArrow_snd_functor
#print axioms productionH1CoordinateArrow_fst
#print axioms productionH1CoordinateArrow_snd
#print axioms productionH1ArrowComparison

end ConstructionTargets.TwiceSpiralGluingHomology
