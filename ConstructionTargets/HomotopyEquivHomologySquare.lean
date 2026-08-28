import ConstructionTargets.SingularHomologyConcrete

/-!
# Homology transport across a strict square of homotopy equivalences
-/

noncomputable section

namespace ConstructionTargets.HomotopyEquivHomologySquare

open CategoryTheory
open ConstructionTargets.SingularHomologyConcrete

/-- The inverse of the homology isomorphism induced by a homotopy equivalence
is the homology map induced by its chosen inverse map. -/
theorem singularHomologyIsoOfHomotopyEquiv_inv_eq_map
    {A A' : Type} [TopologicalSpace A] [TopologicalSpace A']
    (e : ContinuousMap.HomotopyEquiv A A') (n : ℕ) :
    (singularHomologyIsoOfHomotopyEquiv e n).inv =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom e.invFun) := by
  apply (cancel_mono (singularHomologyIsoOfHomotopyEquiv e n).hom).1
  rw [Iso.inv_hom_id, singularHomologyIsoOfHomotopyEquiv_hom]
  rw [← Functor.map_comp]
  change 𝟙 _ = ((AlgebraicTopology.singularHomologyFunctor
    AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom (e.toFun.comp e.invFun))
  rw [singularHomology_map_eq_of_topCatHomotopy
    (continuousMapHomotopyCylinder (Classical.choice e.right_inv))
    (continuousMapHomotopyCylinder_zero (Classical.choice e.right_inv))
    (continuousMapHomotopyCylinder_one (Classical.choice e.right_inv))]
  exact ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
    (AddCommGrpCat.of ℤ)).map_id (TopCat.of A') |>.symm

/-- A strict equality after inserting the chosen source inverse conjugates
the induced singular-homology map through the two homotopy-equivalence
isomorphisms. -/
theorem conjugated_homologyMap_of_strict_square
    {A A' B B' : Type}
    [TopologicalSpace A] [TopologicalSpace A']
    [TopologicalSpace B] [TopologicalSpace B']
    (eA : ContinuousMap.HomotopyEquiv A A')
    (eB : ContinuousMap.HomotopyEquiv B B')
    (f : C(A, B)) (g : C(A', B'))
    (hsq : eB.toFun.comp (f.comp eA.invFun) = g) (n : ℕ) :
    (singularHomologyIsoOfHomotopyEquiv eA n).inv ≫
        ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f) ≫
        (singularHomologyIsoOfHomotopyEquiv eB n).hom =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom g) := by
  rw [singularHomologyIsoOfHomotopyEquiv_inv_eq_map,
    singularHomologyIsoOfHomotopyEquiv_hom]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    (fun q ↦ ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).map q)
    (congrArg TopCat.ofHom hsq)

#print axioms conjugated_homologyMap_of_strict_square

end ConstructionTargets.HomotopyEquivHomologySquare
