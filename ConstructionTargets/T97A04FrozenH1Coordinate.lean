import ConstructionTargets.TorusPiOneWindingCoordinates
import ConstructionTargets.IntegralSingularHomologyComparison

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

end ConstructionTargets.T97A04FrozenH1Coordinate
