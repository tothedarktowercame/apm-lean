import ConstructionTargets.CoefficientSigmaConstFinsuppNaturality
import ConstructionTargets.CoefficientSubcomplexRelativeDegreeRangeOrder

noncomputable section
namespace ConstructionTargets.CoefficientSimplicialChainFinsuppNaturality

open CategoryTheory
open ConstructionTargets.CoefficientSubcomplexMayerVietoris
open ConstructionTargets.CoefficientSigmaConstFinsuppComparison
open ConstructionTargets.CoefficientSigmaConstFinsuppNaturality

variable (R : Type) [CommRing R]

/-- In each degree, a coefficient simplicial-chain map becomes extension along
its map of simplices under the finitely-supported presentations. -/
theorem chainsMap_component_finsupp_naturality {S T : SSet} (f : S ⟶ T) (n : ℕ) :
    ((chains R).map f).f n ≫
        (sigmaConstFinsuppIso R
          (T.obj (Opposite.op (SimplexCategory.mk n)))).hom =
      (sigmaConstFinsuppIso R
          (S.obj (Opposite.op (SimplexCategory.mk n)))).hom ≫
        ModuleCat.ofHom (Finsupp.lmapDomain R R
          (f.app (Opposite.op (SimplexCategory.mk n)))) := by
  change (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of R R)).map
      (f.app (Opposite.op (SimplexCategory.mk n))) ≫ _ = _
  exact sigmaConstFinsuppIso_naturality R _

#print axioms chainsMap_component_finsupp_naturality
end ConstructionTargets.CoefficientSimplicialChainFinsuppNaturality
