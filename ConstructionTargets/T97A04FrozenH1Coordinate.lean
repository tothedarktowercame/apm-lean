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

theorem finiteFreeHurewiczCoordinateMulEquiv_eqToIso_conj
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    {x y : X} (h : x = y) {n : ℕ}
    (piCoordY : FundamentalGroup X y ≃* Multiplicative (Fin n → ℤ))
    (h1Coord : Multiplicative
        (ConstructionTargets.DegreeOneHurewiczMap.IntegralH1 X) ≃*
      Multiplicative (Fin n → ℤ))
    (q : Multiplicative (Fin n → ℤ)) :
    finiteFreeHurewiczCoordinateMulEquiv
        (((eqToIso (congr_arg FundamentalGroupoid.mk h)).conj).trans piCoordY)
        h1Coord q =
      finiteFreeHurewiczCoordinateMulEquiv piCoordY h1Coord q := by
  subst y
  have hconj : (Iso.refl (FundamentalGroupoid.mk x)).conj =
      MulEquiv.refl (FundamentalGroup X x) := by
    ext p
    exact Iso.refl_conj p
  simp only [eqToIso_refl]
  rw [hconj]
  have htrans : (MulEquiv.refl (FundamentalGroup X x)).trans piCoordY =
      piCoordY := by
    ext p
    rfl
  cases htrans
  rfl

theorem frozenTorusAlignedHurewiczCoordinateAtLbarBase_apply
    (q : Multiplicative (Fin 2 → ℤ)) :
    finiteFreeHurewiczCoordinateMulEquiv frozenTorusPi1CoordAtLbarBase
        frozenTorusAlignedH1MulEquivFinTwo q = q := by
  change finiteFreeHurewiczCoordinateMulEquiv
      (((eqToIso (congr_arg FundamentalGroupoid.mk frozenLbar_base)).conj).trans
        frozenTorusPi1Coord)
      frozenTorusAlignedH1MulEquivFinTwo q = q
  rw [finiteFreeHurewiczCoordinateMulEquiv_eqToIso_conj
    (h := frozenLbar_base)]
  exact frozenTorusAlignedHurewiczCoordinate_apply q

theorem frozenLbarIntegralH1_coordinate
    (q : Multiplicative (Fin 2 → ℤ)) :
    frozenTorusAlignedH1MulEquivFinTwo
        (Multiplicative.ofAdd
          ((HomologicalComplex.homologyMap
              (ConstructionTargets.SingularSubdivision.singularPostcomposition
                frozenLbar) 1)
            (Multiplicative.toAdd
              (frozenTorusAlignedH1MulEquivFinTwo.symm q)))) =
      frozenMatrixCoordinateMap q := by
  have h := h1_coordinate_eq_of_fundamentalGroup_coordinate_eq
    frozenLbar frozenTorusPi1Coord frozenTorusPi1CoordAtLbarBase
    frozenTorusAlignedH1MulEquivFinTwo frozenTorusAlignedH1MulEquivFinTwo
    frozenMatrixCoordinateMap frozenLbarPi1Map_coordinateMap_raw q
  rw [frozenTorusAlignedHurewiczCoordinate_apply,
    frozenTorusAlignedHurewiczCoordinateAtLbarBase_apply] at h
  exact h

noncomputable def frozenTorusAlignedH1GroupIsoFinTwo :
    SingularHomology 1 (TopCat.of FrozenTorus) ≅
      AddCommGrpCat.of (Fin 2 → ℤ) :=
  {
  hom := AddCommGrpCat.ofHom
    { toFun := fun a =>
        (frozenTorusAlignedH1MulEquivFinTwo (Multiplicative.ofAdd a)).toAdd
      map_zero' := by
        change (frozenTorusAlignedH1MulEquivFinTwo 1).toAdd = 0
        rw [map_one]
        rfl
      map_add' := by
        intro a b
        change (frozenTorusAlignedH1MulEquivFinTwo
            (Multiplicative.ofAdd a * Multiplicative.ofAdd b)).toAdd = _
        exact congrArg (fun z : Multiplicative _ => z.toAdd)
          (frozenTorusAlignedH1MulEquivFinTwo.map_mul
            (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)) }
  inv := AddCommGrpCat.ofHom
    { toFun := fun v =>
        (frozenTorusAlignedH1MulEquivFinTwo.symm
          (Multiplicative.ofAdd v)).toAdd
      map_zero' := by
        change (frozenTorusAlignedH1MulEquivFinTwo.symm 1).toAdd = 0
        rw [map_one]
        rfl
      map_add' := by
        intro a b
        change (frozenTorusAlignedH1MulEquivFinTwo.symm
            (Multiplicative.ofAdd a * Multiplicative.ofAdd b)).toAdd = _
        exact congrArg (fun z : Multiplicative _ => z.toAdd)
          (frozenTorusAlignedH1MulEquivFinTwo.symm.map_mul
            (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)) }
  hom_inv_id := by
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext _ _
    intro a
    exact congrArg (fun z : Multiplicative _ => z.toAdd)
      (frozenTorusAlignedH1MulEquivFinTwo.symm_apply_apply
        (Multiplicative.ofAdd a))
  inv_hom_id := by
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext _ _
    intro v
    exact congrArg (fun z : Multiplicative _ => z.toAdd)
      (frozenTorusAlignedH1MulEquivFinTwo.apply_symm_apply
        (Multiplicative.ofAdd v)) }

noncomputable def frozenTorusAlignedH1ModuleIsoFinTwo :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of FrozenTorus)) ≅
      ModuleCat.of ℤ (Fin 2 → ℤ) :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of FrozenTorus) 1 _
    frozenTorusAlignedH1GroupIsoFinTwo

theorem frozenLbarIntegralH1_map_commutes :
    (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          frozenLbar) 1) ≫
        frozenTorusAlignedH1GroupIsoFinTwo.hom =
      frozenTorusAlignedH1GroupIsoFinTwo.hom ≫
        AddCommGrpCat.ofHom frozenMatrixAddHom := by
  apply AddCommGrpCat.hom_ext
  apply DFunLike.ext _ _
  intro a
  have h := frozenLbarIntegralH1_coordinate
    (frozenTorusAlignedH1MulEquivFinTwo (Multiplicative.ofAdd a))
  rw [frozenTorusAlignedH1MulEquivFinTwo.symm_apply_apply] at h
  exact congrArg Multiplicative.toAdd h

set_option maxHeartbeats 800000 in
theorem frozenLbarModuleH1_map_commutes :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom frozenLbar)) ≫
        frozenTorusAlignedH1ModuleIsoFinTwo.hom =
      frozenTorusAlignedH1ModuleIsoFinTwo.hom ≫
        ModuleCat.ofHom frozenMatrixAddHom.toIntLinearMap := by
  apply forgetIntModules.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  have hIso : forgetIntModules.map frozenTorusAlignedH1ModuleIsoFinTwo.hom =
      (singularHomologyComparison (TopCat.of FrozenTorus) 1).hom ≫
        frozenTorusAlignedH1GroupIsoFinTwo.hom := by
    unfold frozenTorusAlignedH1ModuleIsoFinTwo
      singularHomologyModuleIsoOfGroupIso moduleIsoOfUnderlyingIso
    exact forgetIntModules.map_preimage _
  rw [hIso]
  change
    forgetIntModules.map
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom frozenLbar)) ≫
        ((singularHomologyComparison (TopCat.of FrozenTorus) 1).hom ≫
          frozenTorusAlignedH1GroupIsoFinTwo.hom) =
      ((singularHomologyComparison (TopCat.of FrozenTorus) 1).hom ≫
        frozenTorusAlignedH1GroupIsoFinTwo.hom) ≫
          AddCommGrpCat.ofHom frozenMatrixAddHom
  rw [← Category.assoc, singularHomologyComparison_naturality]
  simp only [Category.assoc]
  apply congrArg (fun z =>
    (singularHomologyComparison (TopCat.of FrozenTorus) 1).hom ≫ z)
  exact frozenLbarIntegralH1_map_commutes

end ConstructionTargets.T97A04FrozenH1Coordinate
