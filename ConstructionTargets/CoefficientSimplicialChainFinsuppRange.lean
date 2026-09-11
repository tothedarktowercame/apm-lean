import ConstructionTargets.CoefficientSimplicialChainFinsuppNaturality

noncomputable section
namespace ConstructionTargets.CoefficientSimplicialChainFinsuppRange

open CategoryTheory
open ConstructionTargets.CoefficientSubcomplexMayerVietoris
open ConstructionTargets.CoefficientSigmaConstFinsuppComparison
open ConstructionTargets.CoefficientSimplicialChainFinsuppNaturality

variable (R : Type) [CommRing R]

/-- The ambient Finsupp presentation sends the range of a coefficient-chain
component exactly to the range of extension along the simplex map. -/
theorem chainsMap_component_range_finsupp {S T : SSet} (f : S ⟶ T) (n : ℕ) :
    Submodule.map (sigmaConstFinsuppIso R
        (T.obj (Opposite.op (SimplexCategory.mk n)))).hom.hom
      (LinearMap.range (((chains R).map f).f n).hom) =
    LinearMap.range (Finsupp.lmapDomain R R
      (f.app (Opposite.op (SimplexCategory.mk n)))) := by
  let eS := sigmaConstFinsuppIso R
    (S.obj (Opposite.op (SimplexCategory.mk n)))
  let eT := sigmaConstFinsuppIso R
    (T.obj (Opposite.op (SimplexCategory.mk n)))
  let g := Finsupp.lmapDomain R R
    (f.app (Opposite.op (SimplexCategory.mk n)))
  have h := chainsMap_component_finsupp_naturality R f n
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨eS.hom x, ?_⟩
    simpa only [ConcreteCategory.comp_apply] using
      (congrArg (fun k => k x) h).symm
  · rintro ⟨z, rfl⟩
    refine ⟨((chains R).map f).f n (eS.inv z), ⟨eS.inv z, rfl⟩, ?_⟩
    have hx := congrArg (fun k => k (eS.inv z)) h
    change eT.hom (((chains R).map f).f n (eS.inv z)) =
      g (eS.hom (eS.inv z)) at hx
    simpa only [Iso.inv_hom_id_apply] using hx

#print axioms chainsMap_component_range_finsupp
end ConstructionTargets.CoefficientSimplicialChainFinsuppRange
