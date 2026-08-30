import ConstructionTargets.SingularHomologyRetractNonvanishing
import ConstructionTargets.SphereThreeProductMayerVietoris

/-!
# Final product comparison for t95J04

The first-factor retract makes integral `H₂(S² × S⁴)` nonzero.  The reviewed
pole-cover Mayer--Vietoris calculation makes integral `H₂(S³ × S³)` zero.
Transporting singular homology through a hypothetical homeomorphism gives the
contradiction.  No product-homology formula is used.
-/

open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace ConstructionTargets.T95J04FinalProductComparison

open ConstructionTargets.EuclideanSpherePoleOverlapAdapter
open ConstructionTargets.IntegralSingularHomologyComparison
open ConstructionTargets.SingularHomologyRetractNonvanishing
open ConstructionTargets.SphereThreeProductMayerVietoris

/-- The products `S² × S⁴` and `S³ × S³` are not homeomorphic: their integral
degree-two singular homology objects have different vanishing behavior. -/
theorem sphereTwo_product_sphereFour_not_homeomorphic_sphereThree_product_sphereThree :
    ¬ Nonempty
      ((EuclideanSphere 2 × EuclideanSphere 4) ≃ₜ
        (EuclideanSphere 3 × EuclideanSphere 3)) := by
  rintro ⟨e⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)
  have hleft :
      ¬ IsZero (IntegralHomology 2 (EuclideanSphere 2 × EuclideanSphere 4)) :=
    integralHomology_product_not_isZero 2 (canonicalPole 4)
      (positiveSphere_topHomology_not_isZero 2 (by omega))
  have hrightGroup :
      IsZero
        (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
          (TopCat.of (EuclideanSphere 3 × EuclideanSphere 3))) :=
    sphereThreeProduct_singularH2_isZero
  have hright :
      IsZero (IntegralHomology 2 (EuclideanSphere 3 × EuclideanSphere 3)) :=
    singularHomologyModuleIsZeroOfGroupIsZero
      (TopCat.of (EuclideanSphere 3 × EuclideanSphere 3)) 2 hrightGroup
  let eIso :
      TopCat.of (EuclideanSphere 2 × EuclideanSphere 4) ≅
        TopCat.of (EuclideanSphere 3 × EuclideanSphere 3) :=
    TopCat.isoOfHomeo e
  exact hleft (hright.of_iso (F.mapIso eIso))

#print axioms sphereTwo_product_sphereFour_not_homeomorphic_sphereThree_product_sphereThree

end ConstructionTargets.T95J04FinalProductComparison
