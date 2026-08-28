import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.IntegralSingularHomologyComparison

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.EmptyAndSumSingularHomology

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.IntegralSingularHomologyComparison

/-- There are no singular simplices in the empty space. -/
instance (n : ℕ) : IsEmpty (SingularSimplex (TopCat.of Empty) n) :=
  ⟨fun σ => by
    let p : (SimplexCategory.toTop.obj (SimplexCategory.mk n)) :=
      Classical.choice inferInstance
    exact isEmptyElim (σ.down.hom p)⟩

/-- Integral singular chains of the empty space vanish degreewise. -/
theorem emptySingularChains_isZero (n : ℕ) :
    IsZero ((SingularHomologyConcrete.SingularChains (TopCat.of Empty)).X n) := by
  letI := Classical.decEq (SingularSimplex (TopCat.of Empty) n)
  have h : IsZero (AddCommGrpCat.of
      (DirectSum (SingularSimplex (TopCat.of Empty) n) (fun _ => ℤ))) := by
    apply AddCommGrpCat.isZero_of_subsingleton
  exact h.of_iso
    (addCommGrpCoproductIsoDirectSum
      (SingularSimplex (TopCat.of Empty) n))

/-- Integral singular homology of the empty space vanishes in every degree. -/
theorem emptySingularHomology_isZero (n : ℕ) :
    IsZero ((SingularHomologyConcrete.SingularChains (TopCat.of Empty)).homology n) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  exact ShortComplex.exact_of_isZero_X₂ _ (emptySingularChains_isZero n)

/-- The same vanishing in Mathlib's canonical `ModuleCat ℤ` presentation of
integral singular homology. -/
theorem emptyModuleSingularHomology_isZero (n : ℕ) :
    IsZero ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of Empty))) := by
  apply singularHomologyModuleIsZeroOfGroupIsZero
  exact emptySingularHomology_isZero n

#print axioms emptySingularChains_isZero
#print axioms emptySingularHomology_isZero
#print axioms emptyModuleSingularHomology_isZero

end ConstructionTargets.EmptyAndSumSingularHomology
