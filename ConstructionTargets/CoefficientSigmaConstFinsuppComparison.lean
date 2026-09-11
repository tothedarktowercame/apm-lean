import ConstructionTargets.CoefficientSubcomplexSimplexRangeLattice
import Mathlib.LinearAlgebra.DirectSum.Finsupp

noncomputable section
namespace ConstructionTargets.CoefficientSigmaConstFinsuppComparison

open CategoryTheory CategoryTheory.Limits

variable (R : Type) [CommRing R]

noncomputable def sigmaConstFinsuppIso (α : Type) :
    (sigmaConst.obj (ModuleCat.of R R)).obj α ≅ ModuleCat.of R (α →₀ R) := by
  classical
  exact ModuleCat.coprodIsoDirectSum (fun _ : α => ModuleCat.of R R) ≪≫
    (finsuppLEquivDirectSum R R α).symm.toModuleIso

@[simp]
theorem sigma_ι_sigmaConstFinsuppIso_hom (α : Type) (a : α) (r : R) :
    (Sigma.ι (fun _ : α => ModuleCat.of R R) a ≫
      (sigmaConstFinsuppIso R α).hom) r = Finsupp.single a r := by
  classical
  change ((Sigma.ι (fun _ : α => ModuleCat.of R R) a ≫
      (ModuleCat.coprodIsoDirectSum (fun _ : α => ModuleCat.of R R)).hom ≫
      (finsuppLEquivDirectSum R R α).symm.toModuleIso.hom) r) = _
  rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
  exact finsuppLEquivDirectSum_symm_lof R R α a r

#print axioms sigmaConstFinsuppIso
#print axioms sigma_ι_sigmaConstFinsuppIso_hom
end ConstructionTargets.CoefficientSigmaConstFinsuppComparison
