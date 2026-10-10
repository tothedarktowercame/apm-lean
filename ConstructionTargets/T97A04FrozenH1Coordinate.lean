import ConstructionTargets.TorusPiOneWindingCoordinates
import ConstructionTargets.IntegralSingularHomologyComparison
import Mathlib.Topology.Instances.AddCircle.Real

noncomputable section

namespace ConstructionTargets.T97A04FrozenH1Coordinate

open CategoryTheory
open ConstructionTargets.TorusPiOneWindingCoordinates
open ConstructionTargets.CircleHomology
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.IntegralSingularHomologyComparison
open ConstructionTargets.BoundaryTorusIntegralHomologyComplete
open ConstructionTargets.SolidTorusGluingOpenCover

abbrev FrozenTorus := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)
abbrev BoundaryTorus := Circle × ConstructionTargets.SphereHomology.Sphere 1

local instance frozenTorusPathConnectedSpace :
    PathConnectedSpace FrozenTorus where
  nonempty := inferInstance
  joined x y := by
    rcases PathConnectedSpace.joined x.1 y.1 with ⟨p⟩
    rcases PathConnectedSpace.joined x.2 y.2 with ⟨q⟩
    exact ⟨p.prod q⟩

def frozenTorusHomeomorphBoundaryTorus : FrozenTorus ≃ₜ BoundaryTorus :=
  (Homeomorph.prodCongr (AddCircle.homeomorphCircle one_ne_zero)
    (AddCircle.homeomorphCircle one_ne_zero)).trans
      (Homeomorph.prodCongr (Homeomorph.refl Circle) circleHomeomorphSphereOne)

noncomputable def frozenTorusH1GroupIsoFinTwo :
    SingularHomology 1 (TopCat.of FrozenTorus) ≅
      AddCommGrpCat.of (Fin 2 → ℤ) :=
  singularHomologyIsoOfHomotopyEquiv
      frozenTorusHomeomorphBoundaryTorus.toHomotopyEquiv 1 ≪≫
    boundaryTorusH1GroupIsoFinTwo

noncomputable def frozenTorusH1ModuleIsoFinTwo :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of FrozenTorus)) ≅
      ModuleCat.of ℤ (Fin 2 → ℤ) :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of FrozenTorus) 1 _
    frozenTorusH1GroupIsoFinTwo

noncomputable def frozenTorusH1MulEquivFinTwo :
    Multiplicative
        (ConstructionTargets.DegreeOneHurewiczMap.IntegralH1 FrozenTorus) ≃*
      Multiplicative (Fin 2 → ℤ) :=
  AddEquiv.toMultiplicative
    { toFun := frozenTorusH1GroupIsoFinTwo.hom
      invFun := frozenTorusH1GroupIsoFinTwo.inv
      left_inv := frozenTorusH1GroupIsoFinTwo.hom_inv_id_apply
      right_inv := frozenTorusH1GroupIsoFinTwo.inv_hom_id_apply
      map_add' := frozenTorusH1GroupIsoFinTwo.hom.hom.map_add }

open ConstructionTargets.FiniteFreeHurewiczNaturality

noncomputable def frozenTorusAlignedH1MulEquivFinTwo :
    Multiplicative
        (ConstructionTargets.DegreeOneHurewiczMap.IntegralH1 FrozenTorus) ≃*
      Multiplicative (Fin 2 → ℤ) :=
  frozenTorusH1MulEquivFinTwo.trans
    (finiteFreeHurewiczCoordinateMulEquiv
      frozenTorusPi1Coord frozenTorusH1MulEquivFinTwo).symm

theorem frozenTorusAlignedHurewiczCoordinate_apply
    (q : Multiplicative (Fin 2 → ℤ)) :
    finiteFreeHurewiczCoordinateMulEquiv frozenTorusPi1Coord
        frozenTorusAlignedH1MulEquivFinTwo q = q := by
  change
    (finiteFreeHurewiczCoordinateMulEquiv
      frozenTorusPi1Coord frozenTorusH1MulEquivFinTwo).symm
        (finiteFreeHurewiczCoordinateMulEquiv
          frozenTorusPi1Coord frozenTorusH1MulEquivFinTwo q) = q
  exact (finiteFreeHurewiczCoordinateMulEquiv
    frozenTorusPi1Coord frozenTorusH1MulEquivFinTwo).symm_apply_apply q

def frozenMatrixAddHom : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun v := fun i => Fin.cases (2 * v 0 + v 1) (fun _ => v 1 - v 0) i
  map_zero' := by
    funext i
    by_cases hi : i = 0
    · simp [hi]
    · have hi' : i = 1 := Fin.eq_one_of_ne_zero i hi
      subst i
      rfl
  map_add' x y := by
    funext i
    by_cases hi : i = 0
    · simp [hi]
      ring
    · have hi' : i = 1 := Fin.eq_one_of_ne_zero i hi
      subst i
      change (x 1 + y 1) - (x 0 + y 0) = (x 1 - x 0) + (y 1 - y 0)
      ring

def frozenMatrixCoordinateMap :
    Multiplicative (Fin 2 → ℤ) →* Multiplicative (Fin 2 → ℤ) :=
  AddMonoidHom.toMultiplicative frozenMatrixAddHom

theorem frozenLbarPi1Map_coordinateMap
    (p : FundamentalGroup FrozenTorus (0, 0)) :
    frozenMatrixCoordinateMap (frozenTorusPi1Coord p) =
      frozenTorusPi1Coord (frozenLbarPi1Map p) := by
  apply Multiplicative.toAdd.injective
  change (fun i => Fin.cases
      (2 * (frozenTorusPi1Coord p).toAdd 0 +
        (frozenTorusPi1Coord p).toAdd 1)
      (fun _ => (frozenTorusPi1Coord p).toAdd 1 -
        (frozenTorusPi1Coord p).toAdd 0) i) =
    (frozenTorusPi1Coord (frozenLbarPi1Map p)).toAdd
  exact (frozenLbarPi1Map_naturality p).symm

noncomputable def frozenTorusPi1CoordAtLbarBase :
    FundamentalGroup FrozenTorus (frozenLbar (0, 0)) ≃*
      Multiplicative (Fin 2 → ℤ) := by
  exact ((eqToIso (congr_arg FundamentalGroupoid.mk frozenLbar_base)).conj).trans
    frozenTorusPi1Coord

theorem frozenLbarPi1Map_coordinateMap_raw
    (p : FundamentalGroup FrozenTorus (0, 0)) :
    frozenMatrixCoordinateMap (frozenTorusPi1Coord p) =
      frozenTorusPi1CoordAtLbarBase
        (FundamentalGroup.map frozenLbar (0, 0) p) := by
  exact frozenLbarPi1Map_coordinateMap p

end ConstructionTargets.T97A04FrozenH1Coordinate
