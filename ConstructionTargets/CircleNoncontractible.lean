import ConstructionTargets.CircleSingularHomology

/-! # The topological circle is not contractible

The proof combines the existing concrete calculation `H₁(S¹; ℤ) ≅ ℤ` with
homotopy invariance: positive-degree singular homology of a contractible space
is zero.  It introduces no noncontractibility or homology assumptions.
-/

open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace ConstructionTargets.CircleNoncontractible

open ConstructionTargets.SingularHomologyConcrete

abbrev CircleH1 :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle))

theorem moduleHomology_map_eq_of_homotopy
    {X Y : TopCat} {f g : X ⟶ Y}
    (h : MonoidalCategoryStruct.tensorObj X TopCat.I ⟶ Y)
    (h₀ : TopCat.ι₀ ≫ h = f) (h₁ : TopCat.ι₁ ≫ h = g) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map f =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map g := by
  simpa [AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using
    singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy
      (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
      (f := TopCat.toSSet.map f) (g := TopCat.toSSet.map g)
      (H := (topCatHomotopyToSSet h h₀ h₁).toSimplicialObjectHomotopy) 1

theorem circle_not_contractible : ¬ ContractibleSpace Circle := by
  intro h
  letI : ContractibleSpace Circle := h
  obtain ⟨q, hnull⟩ := id_nullhomotopic Circle
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  let u : TopCat.of Circle ⟶ TopCat.of Unit := TopCat.ofHom ⟨fun _ => (), continuous_const⟩
  let c : TopCat.of Unit ⟶ TopCat.of Circle := TopCat.ofHom (ContinuousMap.const Unit q)
  have hpoint : IsZero (F.obj (TopCat.of Unit)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) 1 (ModuleCat.of ℤ ℤ) (TopCat.of Unit) (by norm_num)
  have hconst : F.map (u ≫ c) = 0 := by
    rw [F.map_comp]
    rw [hpoint.eq_of_src (F.map c) 0, comp_zero]
  have hmaps : F.map (𝟙 (TopCat.of Circle)) = F.map (u ≫ c) := by
    apply moduleHomology_map_eq_of_homotopy
      (continuousMapHomotopyCylinder (Classical.choice hnull))
    · exact continuousMapHomotopyCylinder_zero (Classical.choice hnull)
    · rw [continuousMapHomotopyCylinder_one (Classical.choice hnull)]
      ext x
      rfl
  have hid : 𝟙 CircleH1 = 0 := by
    simpa [F, hconst] using hmaps
  have hgen := congrArg (fun f : CircleH1 ⟶ CircleH1 =>
    f circleSingularH1Generator) hid
  apply circleSingularH1Generator_ne_zero
  simpa using hgen

#print axioms moduleHomology_map_eq_of_homotopy
#print axioms circle_not_contractible

end ConstructionTargets.CircleNoncontractible
