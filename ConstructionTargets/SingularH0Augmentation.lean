import ConstructionTargets.T02A06SphereH0
import ConstructionTargets.IntegralSingularHomologyComparison

/-!
# The canonical augmentation of integral singular zeroth homology

The coefficient-sum map on singular zero-chains kills every singular
boundary, so it descends to zeroth homology without any connectedness
hypothesis.  This file also records its naturality under continuous maps.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.SingularH0Augmentation

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.T02A06SphereH0
open ConstructionTargets.IntegralSingularHomologyComparison

private abbrev Chains (X : Type) [TopologicalSpace X] :=
  ConstructionTargets.SingularHomologyConcrete.SingularChains (TopCat.of X)

/-- The coefficient sum of the boundary of every singular one-chain is zero. -/
theorem boundary_comp_zeroChainAugmentation_eq_zero
    {X : Type} [TopologicalSpace X] :
    (Chains X).d 1 0 ≫
        zeroChainAugmentation (X := X) = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  change ConstructionTargets.SingularSubdivision.singularGenerator
      (TopCat.of X) 1 s ≫ (Chains X).d 1 0 ≫
        zeroChainAugmentation = 0
  rw [← Category.assoc,
    ConstructionTargets.SingularSubdivision.singularGenerator_boundary,
    Fin.sum_univ_two, Preadditive.add_comp, Preadditive.zsmul_comp]
  simp only [ConstructionTargets.SingularSubdivision.singularGenerator,
    zeroChainAugmentation]
  simp only [id_eq]
  norm_num
  erw [Limits.Sigma.ι_desc
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
        (TopCat.of X) 0 ↦ 𝟙 (AddCommGrpCat.of ℤ)) _,
    Limits.Sigma.ι_desc
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
        (TopCat.of X) 0 ↦ 𝟙 (AddCommGrpCat.of ℤ)) _]
  simp

/-- The coefficient sum on zero-cycles. -/
noncomputable def cyclesAugmentation
    {X : Type} [TopologicalSpace X] :
    (Chains X).cycles 0 ⟶ AddCommGrpCat.of ℤ :=
  (Chains X).iCycles 0 ≫ zeroChainAugmentation

theorem toCycles_comp_cyclesAugmentation_eq_zero
    {X : Type} [TopologicalSpace X] :
    (Chains X).toCycles 1 0 ≫
        cyclesAugmentation (X := X) = 0 := by
  rw [cyclesAugmentation, ← Category.assoc,
    HomologicalComplex.toCycles_i,
    boundary_comp_zeroChainAugmentation_eq_zero]

/-- The canonical integral augmentation `H₀(X) ⟶ ℤ`, defined for every
topological space and without a connectedness hypothesis. -/
noncomputable def h0Augmentation
    {X : Type} [TopologicalSpace X] :
    SingularHomology 0 (TopCat.of X) ⟶ AddCommGrpCat.of ℤ :=
  ((Chains X).homologyIsCokernel 1 0 (by simp)).desc
    (CokernelCofork.ofπ (cyclesAugmentation (X := X))
      (toCycles_comp_cyclesAugmentation_eq_zero (X := X)))

@[reassoc]
theorem homologyπ_comp_h0Augmentation
    {X : Type} [TopologicalSpace X] :
    (Chains X).homologyπ 0 ≫ h0Augmentation =
      cyclesAugmentation (X := X) := by
  dsimp [h0Augmentation]
  exact Cofork.IsColimit.π_desc
    ((Chains X).homologyIsCokernel 1 0 (by simp))

theorem zeroChainH0Class_comp_h0Augmentation
    {X : Type} [TopologicalSpace X] :
    zeroChainH0Class (X := X) ≫ h0Augmentation =
      zeroChainAugmentation := by
  change zeroChainsToCycles ≫ (Chains X).homologyπ 0 ≫
      h0Augmentation = zeroChainAugmentation
  rw [homologyπ_comp_h0Augmentation]
  simp [cyclesAugmentation]

/-- Postcomposition of singular zero-chains preserves coefficient sum. -/
theorem chainMap_comp_zeroChainAugmentation
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    (singularPostcomposition f).f 0 ≫ zeroChainAugmentation (X := Y) =
      zeroChainAugmentation (X := X) := by
  apply Limits.Sigma.hom_ext
  intro s
  let τ := ConstructionTargets.SingularSubdivision.continuousMapOfSingularSimplex
    0 s
  change ConstructionTargets.SingularSubdivision.singularGenerator
      (TopCat.of X) 0 s ≫ (singularPostcomposition f).f 0 ≫
        zeroChainAugmentation =
    ConstructionTargets.SingularSubdivision.singularGenerator
      (TopCat.of X) 0 s ≫ zeroChainAugmentation
  rw [← Category.assoc]
  change ConstructionTargets.SingularSubdivision.singularGenerator
      (TopCat.of X) 0
        (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
          (TopCat.of X) 0 τ) ≫ (singularPostcomposition f).f 0 ≫
          zeroChainAugmentation = _
  rw [← Category.assoc,
    ConstructionTargets.SingularSubdivision.singularGenerator_singularPostcomposition]
  simp only [ConstructionTargets.SingularSubdivision.singularGenerator,
    zeroChainAugmentation]
  erw [Limits.Sigma.ι_desc
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
        (TopCat.of Y) 0 ↦ 𝟙 (AddCommGrpCat.of ℤ)) _,
    Limits.Sigma.ι_desc
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
        (TopCat.of X) 0 ↦ 𝟙 (AddCommGrpCat.of ℤ)) _]

/-- The canonical zero-chain class is natural under continuous maps. -/
theorem zeroChainH0Class_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    zeroChainH0Class (X := X) ≫
        HomologicalComplex.homologyMap (singularPostcomposition f) 0 =
      (singularPostcomposition f).f 0 ≫ zeroChainH0Class (X := Y) := by
  let KX := Chains X
  let KY := Chains Y
  have hcycles :
      zeroChainsToCycles (X := X) ≫
          HomologicalComplex.cyclesMap (singularPostcomposition f) 0 =
        (singularPostcomposition f).f 0 ≫ zeroChainsToCycles (X := Y) := by
    apply (cancel_mono (KY.iCycles 0)).1
    calc
      (zeroChainsToCycles ≫
          HomologicalComplex.cyclesMap (singularPostcomposition f) 0) ≫
          KY.iCycles 0 =
        zeroChainsToCycles ≫
          (HomologicalComplex.cyclesMap (singularPostcomposition f) 0 ≫
            KY.iCycles 0) := by rw [Category.assoc]
      _ = zeroChainsToCycles ≫
          (KX.iCycles 0 ≫ (singularPostcomposition f).f 0) := by
        rw [HomologicalComplex.cyclesMap_i]
      _ = (zeroChainsToCycles ≫ KX.iCycles 0) ≫
          (singularPostcomposition f).f 0 := by rw [Category.assoc]
      _ = (singularPostcomposition f).f 0 := by
        rw [zeroChainsToCycles_i, Category.id_comp]
      _ = ((singularPostcomposition f).f 0 ≫ zeroChainsToCycles) ≫
          KY.iCycles 0 := by
        rw [Category.assoc, zeroChainsToCycles_i, Category.comp_id]
  change zeroChainsToCycles ≫ KX.homologyπ 0 ≫
      HomologicalComplex.homologyMap (singularPostcomposition f) 0 =
    (singularPostcomposition f).f 0 ≫ zeroChainsToCycles ≫
      KY.homologyπ 0
  calc
    _ = (zeroChainsToCycles ≫
          HomologicalComplex.cyclesMap (singularPostcomposition f) 0) ≫
        KY.homologyπ 0 := by
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    _ = ((singularPostcomposition f).f 0 ≫ zeroChainsToCycles) ≫
        KY.homologyπ 0 := by rw [hcycles]
    _ = _ := by rw [Category.assoc]

/-- The integral `H₀` augmentation is natural under every continuous map. -/
theorem h0Augmentation_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    HomologicalComplex.homologyMap (singularPostcomposition f) 0 ≫
        h0Augmentation (X := Y) =
      h0Augmentation (X := X) := by
  apply (cancel_epi (zeroChainH0Class (X := X))).1
  calc
    zeroChainH0Class (X := X) ≫
          (HomologicalComplex.homologyMap (singularPostcomposition f) 0 ≫
            h0Augmentation (X := Y)) =
        (zeroChainH0Class (X := X) ≫
          HomologicalComplex.homologyMap (singularPostcomposition f) 0) ≫
            h0Augmentation (X := Y) := by rw [Category.assoc]
    _ = ((singularPostcomposition f).f 0 ≫
          zeroChainH0Class (X := Y)) ≫ h0Augmentation (X := Y) := by
      rw [zeroChainH0Class_naturality]
      rfl
    _ = (singularPostcomposition f).f 0 ≫
          (zeroChainH0Class (X := Y) ≫ h0Augmentation (X := Y)) := by
      rw [Category.assoc]
    _ = (singularPostcomposition f).f 0 ≫
          zeroChainAugmentation (X := Y) := by
      rw [zeroChainH0Class_comp_h0Augmentation]
    _ = zeroChainAugmentation (X := X) := chainMap_comp_zeroChainAugmentation f
    _ = zeroChainH0Class (X := X) ≫ h0Augmentation (X := X) :=
      zeroChainH0Class_comp_h0Augmentation.symm

/-- A chosen point splits the unrestricted `H₀` augmentation. -/
theorem singularVertexH0Class_comp_h0Augmentation
    {X : Type} [TopologicalSpace X] (x : X) :
    singularVertexH0Class x ≫ h0Augmentation = 𝟙 _ := by
  let s := ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
    (TopCat.of X) 0 (singularVertexAt x)
  let g := ConstructionTargets.SingularSubdivision.singularGenerator
    (TopCat.of X) 0 s
  have hg : g ≫ zeroChainH0Class = singularVertexH0Class x :=
    singularGenerator_zeroChainH0Class s
  rw [← hg, Category.assoc, zeroChainH0Class_comp_h0Augmentation]
  change Limits.Sigma.ι
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
        (TopCat.of X) 0 ↦ AddCommGrpCat.of ℤ) s ≫
      Limits.Sigma.desc (fun _ ↦ 𝟙 (AddCommGrpCat.of ℤ)) = 𝟙 _
  exact Limits.Sigma.ι_desc _ _

/-- An explicit integral `H₀(X) ≅ ℤ` coordinate rules out the empty
space.  No nonemptiness premise is used. -/
theorem nonempty_of_singularH0_iso_int
    {X : Type} [TopologicalSpace X]
    (e : SingularHomology 0 (TopCat.of X) ≅ AddCommGrpCat.of ℤ) :
    Nonempty X := by
  apply not_isEmpty_iff.mp
  intro hX
  letI : IsEmpty X := hX
  have hchains : IsZero ((Chains X).X 0) := by
    rw [IsZero.iff_id_eq_zero]
    apply Limits.Sigma.hom_ext
    intro s
    exact isEmptyElim
      ((TopCat.toSSetObjEquiv (TopCat.of X)
        (Opposite.op (SimplexCategory.mk 0)) s)
        (Classical.choice inferInstance))
  have hcycles : IsZero ((Chains X).cycles 0) :=
    IsZero.of_mono ((Chains X).iCycles 0) hchains
  letI : Epi ((Chains X).homologyπ 0) :=
    Limits.epi_of_isColimit_cofork
      ((Chains X).homologyIsCokernel 1 0 (by simp))
  have hhomology' : IsZero ((Chains X).homology 0) :=
    IsZero.of_epi ((Chains X).homologyπ 0) hcycles
  have hhomology : IsZero (SingularHomology 0 (TopCat.of X)) := hhomology'
  have hint : IsZero (AddCommGrpCat.of ℤ) := hhomology.of_iso e.symm
  haveI : Subsingleton (AddCommGrpCat.of ℤ) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hint
  exact one_ne_zero (Subsingleton.elim (1 : ℤ) 0)

/-- Module-valued integral singular `H₀ ≅ ℤ` also forces the space to
be nonempty, by the canonical comparison with additive-group homology. -/
theorem nonempty_of_module_singularH0_iso_int
    {X : Type} [TopologicalSpace X]
    (e : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) ≅ ModuleCat.of ℤ ℤ) :
    Nonempty X := by
  apply nonempty_of_singularH0_iso_int
  exact (singularHomologyComparison (TopCat.of X) 0).symm ≪≫
    forgetIntModules.mapIso e

/-- For a nonempty space with infinite-cyclic integral `H₀`, the canonical
augmentation is an isomorphism. -/
noncomputable instance h0Augmentation_isIso_of_iso_int
    {X : Type} [TopologicalSpace X] [Nonempty X]
    (e : SingularHomology 0 (TopCat.of X) ≅ AddCommGrpCat.of ℤ) :
    IsIso (h0Augmentation (X := X)) := by
  let x : X := Classical.choice inferInstance
  have hsplit : singularVertexH0Class x ≫ h0Augmentation = 𝟙 _ :=
    singularVertexH0Class_comp_h0Augmentation x
  letI : Epi (h0Augmentation (X := X)) :=
    (SplitEpi.mk (singularVertexH0Class x) hsplit).epi
  let a : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
    e.inv ≫ h0Augmentation
  letI : Epi a := epi_comp _ _
  letI : Mono a := intGroup_epi_endomorphism_mono a
  have ha : h0Augmentation (X := X) = e.hom ≫ a := by
    simp [a]
  haveI : Mono (h0Augmentation (X := X)) := by
    rw [ha]
    infer_instance
  exact isIso_of_mono_of_epi _

/-- Any continuous map between nonempty spaces with infinite-cyclic integral
`H₀` induces an isomorphism on `H₀`. -/
theorem h0Map_isIso_of_iso_int
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [Nonempty Y] (f : C(X, Y))
    (eX : SingularHomology 0 (TopCat.of X) ≅ AddCommGrpCat.of ℤ)
    (eY : SingularHomology 0 (TopCat.of Y) ≅ AddCommGrpCat.of ℤ) :
    IsIso (HomologicalComplex.homologyMap (singularPostcomposition f) 0) := by
  letI : IsIso (h0Augmentation (X := X)) :=
    h0Augmentation_isIso_of_iso_int (X := X) eX
  let hy : IsIso (h0Augmentation (X := Y)) :=
    h0Augmentation_isIso_of_iso_int (X := Y) eY
  letI : IsIso (h0Augmentation (X := Y)) := hy
  have hcomp : IsIso
      (HomologicalComplex.homologyMap (singularPostcomposition f) 0 ≫
        h0Augmentation (X := Y)) := by
    rw [h0Augmentation_naturality]
    exact h0Augmentation_isIso_of_iso_int (X := X) eX
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (HomologicalComplex.homologyMap (singularPostcomposition f) 0)
    (h0Augmentation (X := Y)) hy hcomp

end ConstructionTargets.SingularH0Augmentation

#print axioms ConstructionTargets.SingularH0Augmentation.h0Augmentation
#print axioms ConstructionTargets.SingularH0Augmentation.zeroChainH0Class_comp_h0Augmentation
#print axioms ConstructionTargets.SingularH0Augmentation.h0Augmentation_naturality
#print axioms ConstructionTargets.SingularH0Augmentation.nonempty_of_singularH0_iso_int
#print axioms ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int
#print axioms ConstructionTargets.SingularH0Augmentation.h0Map_isIso_of_iso_int
