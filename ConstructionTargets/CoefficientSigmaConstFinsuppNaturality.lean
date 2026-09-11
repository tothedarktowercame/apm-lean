import ConstructionTargets.CoefficientSigmaConstFinsuppComparison

noncomputable section
namespace ConstructionTargets.CoefficientSigmaConstFinsuppNaturality

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.CoefficientSigmaConstFinsuppComparison

variable (R : Type) [CommRing R]

/-- The concrete finitely-supported presentation is natural in the coproduct
index type. -/
theorem sigmaConstFinsuppIso_naturality {α β : Type} (f : α → β) :
    (sigmaConst.obj (ModuleCat.of R R)).map f ≫
        (sigmaConstFinsuppIso R β).hom =
      (sigmaConstFinsuppIso R α).hom ≫
        ModuleCat.ofHom (Finsupp.lmapDomain R R f) := by
  classical
  apply Sigma.hom_ext
  intro a
  change (Sigma.ι (fun _ : α => ModuleCat.of R R) a ≫
      Sigma.map' f (fun _ => 𝟙 _) ≫ (sigmaConstFinsuppIso R β).hom) = _
  rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (sigmaConstFinsuppIso R β).hom
      ((Sigma.ι (fun _ : β => ModuleCat.of R R) (f a)) r) =
    Finsupp.mapDomain f
      ((sigmaConstFinsuppIso R α).hom
        ((Sigma.ι (fun _ : α => ModuleCat.of R R) a) r))
  calc
    _ = Finsupp.single (f a) r := by
      simpa only [ConcreteCategory.comp_apply] using
        sigma_ι_sigmaConstFinsuppIso_hom R β (f a) r
    _ = Finsupp.mapDomain f (Finsupp.single a r) := by
      rw [Finsupp.mapDomain_single]
    _ = _ := by
      congr 1
      symm
      simpa only [ConcreteCategory.comp_apply] using
        sigma_ι_sigmaConstFinsuppIso_hom R α a r

#print axioms sigmaConstFinsuppIso_naturality
end ConstructionTargets.CoefficientSigmaConstFinsuppNaturality
