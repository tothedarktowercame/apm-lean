import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Concrete singular homology

Mathlib at this revision has a singular-chain functor from topological spaces
and computes totally disconnected spaces, but has no concrete computation for
the circle, torus, or positive-dimensional spheres. This file first records a
non-vacuous computation for the genuine singular homology of a point, then the
standard CW chain model of `S¹`, with one vertex and one oriented edge. Its
degree-one boundary is zero and it has no degree-two cells, so its first
homology is `ℤ / 0`.

The names deliberately say `CellularModel`: no theorem below claims that the
model is yet singular homology of the topological circle.  The missing
cellular/singular comparison is the precise next construction target.
-/

noncomputable section

namespace ConstructionTargets.SingularHomologyConcrete

open CategoryTheory CategoryTheory.Limits ZeroObject
open CategoryTheory.MonoidalCategory

section DirectDiscreteH0

universe u v

variable (C : Type u) [Category.{v} C] [HasCoproducts.{0} C]
  [Preadditive C] [HasZeroObject C] [CategoryWithHomology C] (R : C)

def pointInclusion {X : Type} [TopologicalSpace X] (p : X) :
    TopCat.of Unit ⟶ TopCat.of X :=
  TopCat.ofHom (ContinuousMap.const Unit p)

noncomputable abbrev discreteSingularChainIso
    (X : Type) [TopologicalSpace X] [TotallyDisconnectedSpace X] :=
  AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
    C R (TopCat.of X)

/-- Direct coordinates on degree-zero opcycles. -/
noncomputable def directDiscreteOpcyclesIso
    (X : Type) [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
        (TopCat.of X)).opcycles 0 ≅ ∐ fun _ : X ↦ R where
  hom := (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
      (TopCat.of X)).descOpcycles
        ((discreteSingularChainIso C R X).hom.f 0) 1 (by simp) (by
          simpa using (discreteSingularChainIso C R X).hom.comm 1 0 |>.symm)
  inv := (discreteSingularChainIso C R X).inv.f 0 ≫
    (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
      (TopCat.of X)).pOpcycles 0
  hom_inv_id := by
    rw [← cancel_epi ((((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
      (TopCat.of X)).pOpcycles 0)]
    simp only [HomologicalComplex.p_descOpcycles_assoc]
    have h : (discreteSingularChainIso C R X).hom.f 0 ≫
        (discreteSingularChainIso C R X).inv.f 0 = 𝟙 _ := by
      change ((discreteSingularChainIso C R X).hom ≫
        (discreteSingularChainIso C R X).inv).f 0 = _
      rw [(discreteSingularChainIso C R X).hom_inv_id]
      rfl
    calc
      _ = ((discreteSingularChainIso C R X).hom.f 0 ≫
          (discreteSingularChainIso C R X).inv.f 0) ≫
          (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
            (TopCat.of X)).pOpcycles 0 := Category.assoc _ _ _ |>.symm
      _ = 𝟙 _ ≫ (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
            (TopCat.of X)).pOpcycles 0 := by rw [h]
      _ = _ := by simp
  inv_hom_id := by
    simp only [Category.assoc, HomologicalComplex.p_descOpcycles]
    change ((discreteSingularChainIso C R X).inv ≫
      (discreteSingularChainIso C R X).hom).f 0 = _
    rw [(discreteSingularChainIso C R X).inv_hom_id]
    rfl

/-- Direct degree-zero coordinates, obtained from the chain isomorphism before
passing through Mathlib's objectwise homology computation. -/
noncomputable def directDiscreteH0Iso
    (X : Type) [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    ((((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
        (TopCat.of X)).homology 0) ≅ ∐ fun _ : X ↦ R :=
  (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
    (TopCat.of X)).isoHomologyι₀ ≪≫ directDiscreteOpcyclesIso C R X

theorem toSSetIsoConst_pointInclusion_naturality
    {X : Type} [TopologicalSpace X] [TotallyDisconnectedSpace X] (p : X) :
    TopCat.toSSet.map (pointInclusion p) ≫ (TopCat.toSSetIsoConst (TopCat.of X)).hom =
      (TopCat.toSSetIsoConst (TopCat.of Unit)).hom ≫
        (Functor.const SimplexCategoryᵒᵖ).map (fun _ : Unit ↦ p) := by
  ext n s
  rfl

omit [HasZeroObject C] [CategoryWithHomology C] in
theorem discreteSingularChainIso_point_naturality
    {X : Type} [TopologicalSpace X] [TotallyDisconnectedSpace X] (p : X) :
    ((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
          (pointInclusion p) ≫ (discreteSingularChainIso C R X).hom =
      (discreteSingularChainIso C R Unit).hom ≫
        ChainComplex.alternatingConst.map
          (Limits.Sigma.map' (fun _ : Unit ↦ p) (fun _ ↦ 𝟙 R)) := by
  ext n
  apply Limits.Sigma.hom_ext
  intro s
  simp [discreteSingularChainIso,
    AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor, pointInclusion]
  change Limits.Sigma.ι (fun _ : X ↦ R) p ≫
      (AlgebraicTopology.alternatingFaceMapComplexConst.hom.app
        (∐ fun _ : X ↦ R)).f n = _
  let q := Limits.Sigma.map' (f := fun _ : Unit ↦ R) (g := fun _ : X ↦ R)
    (fun _ : Unit ↦ p) (fun _ ↦ 𝟙 R)
  have hn := congrArg (fun k ↦ k.f n)
    (AlgebraicTopology.alternatingFaceMapComplexConst.hom.naturality q)
  simp only [HomologicalComplex.comp_f] at hn
  simpa [q, Limits.Sigma.ι_comp_map', Category.assoc] using
    congrArg (fun k ↦ Limits.Sigma.ι (fun _ : Unit ↦ R)
      ((TopCat.toSSetIsoConst (TopCat.of Unit)).hom.app
        (Opposite.op (SimplexCategory.mk n)) s) ≫ k) hn

/-- Under the direct coordinates, a point inclusion on `H₀` is exactly the
corresponding coproduct injection. -/
theorem directDiscreteH0Iso_pointInclusion
    {X : Type} [TopologicalSpace X] [TotallyDisconnectedSpace X] (p : X) :
    Limits.Sigma.ι (fun _ : Unit ↦ R) () ≫
        (directDiscreteH0Iso C R Unit).inv ≫
        HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
            (pointInclusion p)) 0 =
      Limits.Sigma.ι (fun _ : X ↦ R) p ≫
        (directDiscreteH0Iso C R X).inv := by
  dsimp [directDiscreteH0Iso, directDiscreteOpcyclesIso]
  simp only [Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality,
    HomologicalComplex.p_opcyclesMap_assoc]
  let q := ChainComplex.alternatingConst.map
    (Limits.Sigma.map' (f := fun _ : Unit ↦ R) (g := fun _ : X ↦ R)
      (fun _ : Unit ↦ p) (fun _ ↦ 𝟙 R))
  have hn := congrArg (fun f ↦ f.f 0)
    (discreteSingularChainIso_point_naturality C R p)
  have hUI : (discreteSingularChainIso C R Unit).inv.f 0 ≫
      (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
        (pointInclusion p)).f 0 =
      q.f 0 ≫ (discreteSingularChainIso C R X).inv.f 0 := by
    have hX : (discreteSingularChainIso C R X).hom.f 0 ≫
        (discreteSingularChainIso C R X).inv.f 0 = 𝟙 _ := by
      change ((discreteSingularChainIso C R X).hom ≫
        (discreteSingularChainIso C R X).inv).f 0 = _
      rw [(discreteSingularChainIso C R X).hom_inv_id]
      rfl
    have hU : (discreteSingularChainIso C R Unit).inv.f 0 ≫
        (discreteSingularChainIso C R Unit).hom.f 0 = 𝟙 _ := by
      change ((discreteSingularChainIso C R Unit).inv ≫
        (discreteSingularChainIso C R Unit).hom).f 0 = _
      rw [(discreteSingularChainIso C R Unit).inv_hom_id]
      rfl
    calc
      _ = (discreteSingularChainIso C R Unit).inv.f 0 ≫
          (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
            (pointInclusion p)).f 0 ≫
          (discreteSingularChainIso C R X).hom.f 0 ≫
          (discreteSingularChainIso C R X).inv.f 0 := by
            calc
              _ = ((discreteSingularChainIso C R Unit).inv.f 0 ≫
                  (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
                    (pointInclusion p)).f 0) ≫ 𝟙 _ := by simp
              _ = ((discreteSingularChainIso C R Unit).inv.f 0 ≫
                  (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
                    (pointInclusion p)).f 0) ≫
                  ((discreteSingularChainIso C R X).hom.f 0 ≫
                    (discreteSingularChainIso C R X).inv.f 0) := by rw [hX]
              _ = _ := by simp only [Category.assoc]
      _ = (discreteSingularChainIso C R Unit).inv.f 0 ≫
          (discreteSingularChainIso C R Unit).hom.f 0 ≫ q.f 0 ≫
          (discreteSingularChainIso C R X).inv.f 0 := by
            simpa [q, HomologicalComplex.comp_f, Category.assoc] using
              congrArg (fun k ↦ (discreteSingularChainIso C R Unit).inv.f 0 ≫
                k ≫ (discreteSingularChainIso C R X).inv.f 0) hn
      _ = _ := by
        calc
          _ = ((discreteSingularChainIso C R Unit).inv.f 0 ≫
              (discreteSingularChainIso C R Unit).hom.f 0) ≫
              (q.f 0 ≫ (discreteSingularChainIso C R X).inv.f 0) := by
                simp only [Category.assoc]
          _ = _ := by rw [hU, Category.id_comp]
  calc
    _ = Limits.Sigma.ι (fun _ : Unit ↦ R) () ≫
        (q.f 0 ≫ (discreteSingularChainIso C R X).inv.f 0) ≫
        (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
          (TopCat.of X)).pOpcycles 0 ≫
        (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
          (TopCat.of X)).isoHomologyι₀.inv := by
      simpa [Category.assoc] using congrArg (fun k ↦
        Limits.Sigma.ι (fun _ : Unit ↦ R) () ≫ k ≫
          (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
            (TopCat.of X)).pOpcycles 0 ≫
          (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
            (TopCat.of X)).isoHomologyι₀.inv) hUI
    _ = _ := by simp [q, Category.assoc]

/-- The direct coordinates are natural for maps between totally disconnected
spaces. This is proved at chain level, before taking homology. -/
theorem directDiscreteH0Iso_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
    (f : TopCat.of X ⟶ TopCat.of Y) :
    (directDiscreteH0Iso C R X).inv ≫
        HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map f) 0 =
      Limits.Sigma.map' (f := fun _ : X ↦ R) (g := fun _ : Y ↦ R)
          (fun x ↦ f x) (fun _ ↦ 𝟙 R) ≫
        (directDiscreteH0Iso C R Y).inv := by
  apply Limits.Sigma.hom_ext
  intro x
  let px : TopCat.of Unit ⟶ TopCat.of X := pointInclusion x
  let py : TopCat.of Unit ⟶ TopCat.of Y := pointInclusion (f x)
  have hcomp : px ≫ f = py := by ext; rfl
  have hmap := HomologicalComplex.homologyMap_comp
    (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map px)
    (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map f) 0
  calc
    _ = (Limits.Sigma.ι (fun _ : Unit ↦ R) () ≫
          (directDiscreteH0Iso C R Unit).inv ≫
          HomologicalComplex.homologyMap
            (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map px) 0) ≫
        HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map f) 0 := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫
        HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map f) 0)
        (directDiscreteH0Iso_pointInclusion C R x).symm
    _ = Limits.Sigma.ι (fun _ : Unit ↦ R) () ≫
          (directDiscreteH0Iso C R Unit).inv ≫
          HomologicalComplex.homologyMap
            ((((AlgebraicTopology.singularChainComplexFunctor C).obj R).map px) ≫
              (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map f)) 0 := by
      simp only [Category.assoc, hmap]
    _ = Limits.Sigma.ι (fun _ : Unit ↦ R) () ≫
          (directDiscreteH0Iso C R Unit).inv ≫
          HomologicalComplex.homologyMap
            (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map py) 0 := by
      rw [← Functor.map_comp, hcomp]
    _ = Limits.Sigma.ι (fun _ : Y ↦ R) (f x) ≫
          (directDiscreteH0Iso C R Y).inv :=
      directDiscreteH0Iso_pointInclusion C R (f x)
    _ = _ := by simp

/-- Collapse of a two-point discrete space to a point. -/
def boolCollapse : TopCat.of Bool ⟶ TopCat.of Unit :=
  TopCat.ofHom (ContinuousMap.const Bool ())

/-- In direct degree-zero coordinates, collapsing two points is the
codiagonal: each basis summand maps by the identity to the unique point. -/
theorem directDiscreteH0Iso_boolCollapse_codiagonal :
    (directDiscreteH0Iso C R Bool).inv ≫
        HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
            boolCollapse) 0 ≫
        (directDiscreteH0Iso C R Unit).hom ≫
        (Limits.coproductUniqueIso (fun _ : Unit ↦ R)).hom =
      Limits.Sigma.desc (fun _ : Bool ↦ 𝟙 R) := by
  have hn := directDiscreteH0Iso_naturality C R boolCollapse
  rw [← Category.assoc, ← Category.assoc]
  rw [hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply Limits.Sigma.hom_ext
  intro b
  simp [boolCollapse, Limits.Sigma.ι_desc]
  change colimit.ι (Discrete.functor (fun _ : Unit ↦ R)) (Discrete.mk ()) ≫
      colimit.desc (Discrete.functor (fun _ : Unit ↦ R))
        (colimitCoconeOfUnique (fun _ : Unit ↦ R)).cocone = 𝟙 R
  rw [colimit.ι_desc]
  rfl

end DirectDiscreteH0

/-- Ordinary integer singular chains. -/
abbrev SingularChains (X : TopCat) : ChainComplex AddCommGrpCat ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).obj X

/-- The inclusion of a subspace, equipped with its induced topology. -/
def subspaceInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The map on singular chains induced by a subspace inclusion. -/
noncomputable def singularSubspaceMap {X : Type} [TopologicalSpace X] (A : Set X) :
    SingularChains (TopCat.of A) ⟶ SingularChains (TopCat.of X) :=
  ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (subspaceInclusion A)

/-- The subcomplex generated by singular simplices which factor through `A`.
Using the categorical image makes "generated by" literal and avoids identifying
chains merely by a set-theoretic image condition. -/
noncomputable def relativeSingularSubcomplex
    {X : Type} [TopologicalSpace X] (A : Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  image (singularSubspaceMap A)

/-- Inclusion of the subcomplex of chains supported in `A`. -/
noncomputable def relativeSingularSubcomplex.ι
    {X : Type} [TopologicalSpace X] (A : Set X) :
    relativeSingularSubcomplex A ⟶ SingularChains (TopCat.of X) :=
  image.ι (singularSubspaceMap A)

/-- The boundary of a chain generated in `A` is again generated in `A`.
This is the chain-map square of the image inclusion, recorded explicitly so
the restriction of the differential is a theorem rather than an assertion. -/
theorem relativeSingularSubcomplex_differential_restricts
    {X : Type} [TopologicalSpace X] (A : Set X) (i j : ℕ) :
    (relativeSingularSubcomplex.ι A).f i ≫ (SingularChains (TopCat.of X)).d i j =
      (relativeSingularSubcomplex A).d i j ≫ (relativeSingularSubcomplex.ι A).f j :=
  (relativeSingularSubcomplex.ι A).comm i j

/-- Relative singular chains of `(X,A)`, as the quotient of the absolute
singular complex by the subcomplex generated by simplices factoring through
`A`. -/
noncomputable def RelativeSingularChains
    {X : Type} [TopologicalSpace X] (A : Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel (relativeSingularSubcomplex.ι A)

/-- The canonical projection from absolute to relative singular chains. -/
noncomputable def relativeSingularProjection
    {X : Type} [TopologicalSpace X] (A : Set X) :
    SingularChains (TopCat.of X) ⟶ RelativeSingularChains A :=
  cokernel.π (relativeSingularSubcomplex.ι A)

/-- Taking the image before quotienting does not change the quotient. This is
the bridge to the short exact sequence of a pair in the next construction
stage. -/
noncomputable def relativeSingularChainsIsoCokernelSubspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X) :
    RelativeSingularChains A ≅ cokernel (singularSubspaceMap A) :=
  cokernelImageι (singularSubspaceMap A)

/-- Postcomposition with a subspace inclusion is injective on singular
simplices. -/
theorem subspaceInclusion_singularSimplex_injective
    {X : Type} [TopologicalSpace X] (A : Set X) (n : SimplexCategoryᵒᵖ) :
    Function.Injective
      ((TopCat.toSSet.map (subspaceInclusion A)).app n) := by
  intro s t h
  apply (TopCat.toSSetObjEquiv (TopCat.of A) n).injective
  ext x
  change ((TopCat.toSSetObjEquiv (TopCat.of X) n
    ((TopCat.toSSet.map (subspaceInclusion A)).app n s)) x) =
    ((TopCat.toSSetObjEquiv (TopCat.of X) n
      ((TopCat.toSSet.map (subspaceInclusion A)).app n t)) x)
  exact congrArg (fun k ↦ k x)
    (congrArg (TopCat.toSSetObjEquiv (TopCat.of X) n) h)

/-- In every degree, inclusion of a subspace induces a monomorphism on
integer singular chains. -/
instance singularSubspaceMap_degree_mono
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    Mono ((singularSubspaceMap A).f n) := by
  dsimp [singularSubspaceMap, SingularChains,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  apply MonoCoprod.mono_map'_of_injective
  exact subspaceInclusion_singularSimplex_injective A _

/-- Inclusion of a subspace induces a monomorphism of singular chain
complexes. -/
instance singularSubspaceMap_mono
    {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (singularSubspaceMap A) :=
  HomologicalComplex.mono_of_mono_f _ fun _ ↦ inferInstance

/-- The canonical cokernel short complex for the inclusion of subspace
singular chains. -/
noncomputable def singularPairCokernelShortComplex
    {X : Type} [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (singularSubspaceMap A)
    (cokernel.π (singularSubspaceMap A))
    (cokernel.condition (singularSubspaceMap A))

/-- The short complex of a pair, stated with the actual subspace chains on
the left and the previously defined relative quotient on the right. -/
noncomputable def singularPairShortComplex
    {X : Type} [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (singularSubspaceMap A) (relativeSingularProjection A) (by
    change singularSubspaceMap A ≫
      cokernel.π (image.ι (singularSubspaceMap A)) = 0
    calc
      _ = factorThruImage (singularSubspaceMap A) ≫
          (image.ι (singularSubspaceMap A) ≫
            cokernel.π (image.ι (singularSubspaceMap A))) := by
            simpa only [Category.assoc] using congrArg
              (fun k ↦ k ≫ cokernel.π (image.ι (singularSubspaceMap A)))
              (image.fac (singularSubspaceMap A)).symm
      _ = 0 := by rw [cokernel.condition, comp_zero])

/-- The image quotient and the direct cokernel identify the two presentations
of the short complex of a pair. -/
noncomputable def singularPairShortComplexIsoCokernel
    {X : Type} [TopologicalSpace X] (A : Set X) :
    singularPairCokernelShortComplex A ≅ singularPairShortComplex A :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (relativeSingularChainsIsoCokernelSubspaceMap A).symm
    (by simp [singularPairCokernelShortComplex, singularPairShortComplex])
    (by
      dsimp [singularPairCokernelShortComplex, singularPairShortComplex,
        relativeSingularProjection,
        relativeSingularChainsIsoCokernelSubspaceMap]
      change cokernel.π (image.ι (singularSubspaceMap A)) = _
      symm
      apply cokernel.π_desc)

/-- The singular chain sequence of a pair is short exact. -/
theorem singularPairShortComplex_shortExact
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (singularPairShortComplex A).ShortExact := by
  apply ShortComplex.shortExact_of_iso (singularPairShortComplexIsoCokernel A)
  let S := singularPairCokernelShortComplex A
  have hm : Mono S.f := by
    change Mono (singularSubspaceMap A)
    infer_instance
  have he : Epi S.g := by
    change Epi (cokernel.π (singularSubspaceMap A))
    infer_instance
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel (singularSubspaceMap A))) hm he

/-- The connecting homomorphism in the homology sequence of a pair. -/
noncomputable def singularPairConnecting
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (RelativeSingularChains A).homology (n + 1) ⟶
      (SingularChains (TopCat.of A)).homology n :=
  (singularPairShortComplex_shortExact A).δ (n + 1) n rfl

/-- Exactness at the subspace-homology term in the long exact sequence of a
pair. -/
theorem singularPairHomology_exact_subspace
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk (singularPairConnecting A n)
      (HomologicalComplex.homologyMap (singularSubspaceMap A) n)
      ((singularPairShortComplex_shortExact A).δ_comp (n + 1) n rfl)).Exact :=
  (singularPairShortComplex_shortExact A).homology_exact₁ (n + 1) n rfl

/-- Exactness at the absolute-homology term in the long exact sequence of a
pair. -/
theorem singularPairHomology_exact_absolute
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (singularSubspaceMap A) n)
      (HomologicalComplex.homologyMap (relativeSingularProjection A) n)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        change HomologicalComplex.homologyMap ((singularPairShortComplex A).f ≫
          (singularPairShortComplex A).g) n = 0
        rw [(singularPairShortComplex A).zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  (singularPairShortComplex_shortExact A).homology_exact₂ n

/-- Exactness at the relative-homology term in the long exact sequence of a
pair. -/
theorem singularPairHomology_exact_relative
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (relativeSingularProjection A) (n + 1))
      (singularPairConnecting A n)
      ((singularPairShortComplex_shortExact A).comp_δ (n + 1) n rfl)).Exact :=
  (singularPairShortComplex_shortExact A).homology_exact₃ (n + 1) n rfl

/-- The subspace inclusion of the whole space is an isomorphism. -/
noncomputable def subspaceUnivIso (X : Type) [TopologicalSpace X] :
    TopCat.of (Set.univ : Set X) ≅ TopCat.of X :=
  TopCat.isoOfHomeo (Homeomorph.Set.univ X)

theorem subspaceInclusion_univ (X : Type) [TopologicalSpace X] :
    subspaceInclusion (Set.univ : Set X) = (subspaceUnivIso X).hom :=
  rfl

noncomputable instance singularSubspaceMap_univ_isIso
    (X : Type) [TopologicalSpace X] :
    IsIso (singularSubspaceMap (Set.univ : Set X)) := by
  rw [singularSubspaceMap, subspaceInclusion_univ]
  infer_instance

/-- Sanity check: quotienting a space's chains by all of its chains gives the
zero relative complex. -/
theorem selfRelativeSingularChains_isZero
    (X : Type) [TopologicalSpace X] :
    IsZero (RelativeSingularChains (Set.univ : Set X)) :=
  (isZero_cokernel_of_epi (singularSubspaceMap (Set.univ : Set X))).of_iso
    (relativeSingularChainsIsoCokernelSubspaceMap (Set.univ : Set X))

/-- In the self-pair, every relative homology group vanishes. -/
theorem selfRelativeSingularHomology_isZero
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    IsZero ((RelativeSingularChains (Set.univ : Set X)).homology n) :=
  Functor.map_isZero
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n)
    (selfRelativeSingularChains_isZero X)

/-- A chosen point of the topological zero-simplex. -/
noncomputable def zeroSimplexPoint : stdSimplex ℝ (Fin 1) :=
  Classical.choice inferInstance

/-- Read the value of a singular zero-simplex in the discrete two-point
space. -/
noncomputable def boolZeroSimplexValue
    (s : (TopCat.toSSet.obj (TopCat.of Bool)).obj
      (Opposite.op (SimplexCategory.mk 0))) : Bool :=
  (TopCat.toSSetObjEquiv (TopCat.of Bool)
    (Opposite.op (SimplexCategory.mk 0)) s) zeroSimplexPoint

/-- The degree-zero functional which counts only singular vertices landing at
`true`. -/
noncomputable def boolTrueWeight :
    (SingularChains (TopCat.of Bool)).X 0 ⟶ AddCommGrpCat.of ℤ :=
  Limits.Sigma.desc fun s =>
    if boolZeroSimplexValue s then 𝟙 (AddCommGrpCat.of ℤ) else 0

theorem boolZeroSimplexValue_map_falseSubspace
    (s : (TopCat.toSSet.obj (TopCat.of ({false} : Set Bool))).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    boolZeroSimplexValue
      ((TopCat.toSSet.map (subspaceInclusion ({false} : Set Bool))).app
        (Opposite.op (SimplexCategory.mk 0)) s) = false := by
  change ((TopCat.toSSetObjEquiv (TopCat.of ({false} : Set Bool))
    (Opposite.op (SimplexCategory.mk 0)) s) zeroSimplexPoint).val = false
  exact ((TopCat.toSSetObjEquiv (TopCat.of ({false} : Set Bool))
    (Opposite.op (SimplexCategory.mk 0)) s) zeroSimplexPoint).property

/-- The `true`-vertex weight vanishes on chains coming from the one-point
subspace `{false}`. -/
theorem falseSubspaceMap_comp_boolTrueWeight :
    (singularSubspaceMap ({false} : Set Bool)).f 0 ≫ boolTrueWeight = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  simp [singularSubspaceMap, SingularChains,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor,
    boolTrueWeight, subspaceInclusion]
  rw [Limits.Sigma.ι_desc]
  rw [if_neg (by
    simpa [subspaceInclusion] using boolZeroSimplexValue_map_falseSubspace s)]
  symm
  exact comp_zero

/-- Evaluation in degree zero identifies the degree-zero relative chain group
with the ordinary cokernel of the degree-zero inclusion. -/
noncomputable def relativeDegreeZeroCokernelIso
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (RelativeSingularChains A).X 0 ≅
      cokernel ((relativeSingularSubcomplex.ι A).f 0) :=
  PreservesCokernel.iso (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) 0)
    (relativeSingularSubcomplex.ι A)

theorem falseRelativeSubcomplex_comp_boolTrueWeight :
    (relativeSingularSubcomplex.ι ({false} : Set Bool)).f 0 ≫ boolTrueWeight = 0 := by
  let e := (factorThruImage (singularSubspaceMap ({false} : Set Bool))).f 0
  apply (cancel_epi e).mp
  change e ≫ ((relativeSingularSubcomplex.ι ({false} : Set Bool)).f 0 ≫
    boolTrueWeight) = e ≫ 0
  rw [← Category.assoc]
  change ((factorThruImage (singularSubspaceMap ({false} : Set Bool)) ≫
    relativeSingularSubcomplex.ι ({false} : Set Bool)).f 0) ≫ boolTrueWeight = _
  rw [relativeSingularSubcomplex.ι, image.fac]
  simpa using falseSubspaceMap_comp_boolTrueWeight

/-- The functional on the proper-pair quotient induced by counting the
`true` vertex. -/
noncomputable def falsePairRelativeDegreeZeroWeight :
    (RelativeSingularChains ({false} : Set Bool)).X 0 ⟶ AddCommGrpCat.of ℤ :=
  (relativeDegreeZeroCokernelIso ({false} : Set Bool)).hom ≫
    cokernel.desc _ boolTrueWeight falseRelativeSubcomplex_comp_boolTrueWeight

/-- The constant singular zero-simplex at a chosen Boolean point. -/
noncomputable def boolConstantZeroSimplex (b : Bool) :
    (TopCat.toSSet.obj (TopCat.of Bool)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  (TopCat.toSSetObjEquiv (TopCat.of Bool)
    (Opposite.op (SimplexCategory.mk 0))).symm
      (ContinuousMap.const (stdSimplex ℝ (Fin 1)) b)

/-- The absolute zero-chain consisting of the `true` vertex with coefficient
one. -/
noncomputable def boolTrueZeroChain :
    (SingularChains (TopCat.of Bool)).X 0 :=
  Limits.Sigma.ι
    (fun _ : (TopCat.toSSet.obj (TopCat.of Bool)).obj
      (Opposite.op (SimplexCategory.mk 0)) ↦ AddCommGrpCat.of ℤ)
    (boolConstantZeroSimplex true) 1

@[simp] theorem boolTrueWeight_trueZeroChain :
    boolTrueWeight boolTrueZeroChain = 1 := by
  have hweight : (Limits.Sigma.ι
    (fun _ : (TopCat.toSSet.obj (TopCat.of Bool)).obj
      (Opposite.op (SimplexCategory.mk 0)) ↦ AddCommGrpCat.of ℤ)
    (boolConstantZeroSimplex true) ≫ boolTrueWeight) =
      𝟙 (AddCommGrpCat.of ℤ) := by
    dsimp [boolTrueWeight]
    rw [Limits.Sigma.ι_desc]
    have hv : boolZeroSimplexValue (boolConstantZeroSimplex true) = true := by
      unfold boolZeroSimplexValue boolConstantZeroSimplex
      rw [Equiv.apply_symm_apply]
      rfl
    rw [if_pos hv]
  change (Limits.Sigma.ι
    (fun _ : (TopCat.toSSet.obj (TopCat.of Bool)).obj
      (Opposite.op (SimplexCategory.mk 0)) ↦ AddCommGrpCat.of ℤ)
    (boolConstantZeroSimplex true) ≫ boolTrueWeight) 1 = 1
  rw [hweight]
  rfl

/-- The class of the `true` vertex modulo chains generated by `{false}`. -/
noncomputable def falsePairRelativeTrueClass :
    (RelativeSingularChains ({false} : Set Bool)).X 0 :=
  (relativeSingularProjection ({false} : Set Bool)).f 0 boolTrueZeroChain

theorem relativeProjection_f_zero_comp_cokernelIso
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (relativeSingularProjection A).f 0 ≫ (relativeDegreeZeroCokernelIso A).hom =
      cokernel.π ((relativeSingularSubcomplex.ι A).f 0) := by
  simpa [relativeSingularProjection, relativeDegreeZeroCokernelIso] using
    (PreservesCokernel.π_iso_hom
      (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) 0)
      (relativeSingularSubcomplex.ι A))

/-- The proper-pair class is detected by the independently defined Boolean
vertex weight: it maps to `1 : ℤ`. -/
@[simp] theorem falsePairRelativeDegreeZeroWeight_trueClass :
    falsePairRelativeDegreeZeroWeight falsePairRelativeTrueClass = 1 := by
  change ((relativeSingularProjection ({false} : Set Bool)).f 0 ≫
    (relativeDegreeZeroCokernelIso ({false} : Set Bool)).hom ≫
    cokernel.desc _ boolTrueWeight falseRelativeSubcomplex_comp_boolTrueWeight)
      boolTrueZeroChain = 1
  rw [← Category.assoc, relativeProjection_f_zero_comp_cokernelIso]
  simpa using boolTrueWeight_trueZeroChain

/-- Anti-vacuity for a proper, nonempty pair: the degree-zero relative chain
group of `(Bool,{false})` contains the exhibited nonzero `true`-vertex class. -/
theorem falsePairRelativeTrueClass_ne_zero : falsePairRelativeTrueClass ≠ 0 := by
  intro h
  have hweight := falsePairRelativeDegreeZeroWeight_trueClass
  rw [h, map_zero] at hweight
  exact zero_ne_one hweight

/-- There are no singular simplices in the empty subspace, so its map into
absolute chains is the zero chain map. -/
theorem singularSubspaceMap_empty_eq_zero
    (X : Type) [TopologicalSpace X] :
    singularSubspaceMap (∅ : Set X) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Limits.Sigma.hom_ext
  intro s
  exact isEmptyElim
    ((TopCat.toSSetObjEquiv (TopCat.of (∅ : Set X))
      (Opposite.op (SimplexCategory.mk n)) s)
      (Classical.choice inferInstance))

/-- Sanity check: relative chains for `(X,∅)` recover absolute singular
chains. -/
noncomputable def relativeEmptyIsoAbsolute
    (X : Type) [TopologicalSpace X] :
    RelativeSingularChains (∅ : Set X) ≅ SingularChains (TopCat.of X) := by
  refine relativeSingularChainsIsoCokernelSubspaceMap (∅ : Set X) ≪≫ ?_
  rw [singularSubspaceMap_empty_eq_zero]
  exact cokernelZeroIsoTarget


/-- Ordinary singular homology with integer coefficients, using Mathlib's
singular-chain functor into additive commutative groups. -/
abbrev SingularHomology (n : ℕ) (X : TopCat) : AddCommGrpCat :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
    (AddCommGrpCat.of ℤ)).obj X

/-- The one-point topological space. -/
abbrev Point := TopCat.of Unit

/-- The actual zeroth singular homology of a point is `ℤ`. -/
noncomputable def pointH0IsoInt : SingularHomology 0 Point ≅ AddCommGrpCat.of ℤ :=
  AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
      AddCommGrpCat (AddCommGrpCat.of ℤ) Point ≪≫
    coproductUniqueIso (fun _ : Point ↦ AddCommGrpCat.of ℤ)

/-- The canonical nonzero class in the actual zeroth singular homology of a
point, obtained by transporting `1 : ℤ` through the computed isomorphism. -/
noncomputable def pointH0Generator : SingularHomology 0 Point :=
  pointH0IsoInt.inv 1

@[simp] theorem pointH0IsoInt_hom_generator :
    pointH0IsoInt.hom pointH0Generator = 1 := by
  simp [pointH0Generator]

/-- Anti-vacuity witness for the genuine singular theory: `H₀(*)` contains
the exhibited class corresponding to the independently known integer `1`. -/
theorem pointH0Generator_ne_zero : pointH0Generator ≠ 0 := by
  intro h
  have hgen := pointH0IsoInt_hom_generator
  rw [h, map_zero] at hgen
  exact zero_ne_one hgen

/-- For the self-pair of a point, the first map in the long exact sequence is
an isomorphism. -/
noncomputable def selfPairPointH0InclusionIso :
    (SingularChains (TopCat.of (Set.univ : Set Unit))).homology 0 ≅
      SingularHomology 0 Point := by
  letI := singularSubspaceMap_univ_isIso Unit
  exact HomologicalComplex.homologyMapIso
    (asIso (singularSubspaceMap (Set.univ : Set Unit))) 0

@[simp] theorem selfPairPointH0InclusionIso_hom :
  selfPairPointH0InclusionIso.hom = HomologicalComplex.homologyMap
      (singularSubspaceMap (Set.univ : Set Unit)) 0 := by
  simp [selfPairPointH0InclusionIso]

/-- The self-pair LES class which maps to the already computed generator of
`H₀(*)`. -/
noncomputable def selfPairPointH0LeftGenerator :
    (SingularChains (TopCat.of (Set.univ : Set Unit))).homology 0 :=
  selfPairPointH0InclusionIso.inv pointH0Generator

/-- Anti-vacuity evaluation of the LES: its subspace-to-absolute map sends the
exhibited self-pair class to the point generator, whose independent integer
coordinate is `1`. -/
theorem selfPairPointLES_generator_evaluates_to_one :
    pointH0IsoInt.hom
      (HomologicalComplex.homologyMap
        (singularSubspaceMap (Set.univ : Set Unit)) 0
        selfPairPointH0LeftGenerator) = 1 := by
  rw [← selfPairPointH0InclusionIso_hom]
  change (selfPairPointH0InclusionIso.inv ≫
    selfPairPointH0InclusionIso.hom ≫ pointH0IsoInt.hom) pointH0Generator = 1
  rw [selfPairPointH0InclusionIso.inv_hom_id_assoc]
  exact pointH0IsoInt_hom_generator

/-- All positive-degree singular homology groups of a point vanish. -/
theorem pointHigherHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularHomology n Point) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    AddCommGrpCat n (AddCommGrpCat.of ℤ) Point hn

/-- A cylinder homotopy in `TopCat` induces a simplicial homotopy between the
maps of singular simplicial sets. This supplies the topological-to-simplicial
bridge needed by Mathlib's existing chain-homotopy theorem. -/
noncomputable def topCatHomotopyToSSet
    {X Y : TopCat} {f g : X ⟶ Y} (h : X ⊗ TopCat.I ⟶ Y)
    (h₀ : TopCat.ι₀ ≫ h = f) (h₁ : TopCat.ι₁ ≫ h = g) :
    SSet.Homotopy (TopCat.toSSet.map f) (TopCat.toSSet.map g) where
  h := (TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI) ≫
    Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I ≫ TopCat.toSSet.map h
  h₀ := by
    change _ = TopCat.toSSet.map f
    simp only [SSet.stdSimplex.ι₀_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, h₀]
  h₁ := by
    change _ = TopCat.toSSet.map g
    simp only [SSet.stdSimplex.ι₁_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, h₁]
  rel := by
    ext n x
    exact x.1.property.elim

/-- Topologically homotopic maps induce equal maps on ordinary singular
homology. -/
theorem singularHomology_map_eq_of_topCatHomotopy
    {X Y : TopCat} {f g : X ⟶ Y} (h : X ⊗ TopCat.I ⟶ Y)
    (h₀ : TopCat.ι₀ ≫ h = f) (h₁ : TopCat.ι₁ ≫ h = g) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map f =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map g := by
  simpa [AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using
    singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy
      (C := AddCommGrpCat) (R := AddCommGrpCat.of ℤ)
      (f := TopCat.toSSet.map f) (g := TopCat.toSSet.map g)
      (H := (topCatHomotopyToSSet h h₀ h₁).toSimplicialObjectHomotopy) n

/-- A topological homotopy equivalence, presented by explicit cylinder
homotopies, induces an isomorphism on ordinary singular homology. -/
noncomputable def singularHomologyIsoOfTopCatHomotopyEquivalence
    {X Y : TopCat} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : X ⊗ TopCat.I ⟶ X)
    (hX₀ : TopCat.ι₀ ≫ hX = f ≫ g) (hX₁ : TopCat.ι₁ ≫ hX = 𝟙 X)
    (hY : Y ⊗ TopCat.I ⟶ Y)
    (hY₀ : TopCat.ι₀ ≫ hY = g ≫ f) (hY₁ : TopCat.ι₁ ≫ hY = 𝟙 Y)
    (n : ℕ) : SingularHomology n X ≅ SingularHomology n Y := by
  let F := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
    (AddCommGrpCat.of ℤ)
  letI : IsIso (F.map f) := IsIso.mk ⟨F.map g, by
    rw [← F.map_comp, singularHomology_map_eq_of_topCatHomotopy hX hX₀ hX₁,
      F.map_id], by
    rw [← F.map_comp, singularHomology_map_eq_of_topCatHomotopy hY hY₀ hY₁,
      F.map_id]⟩
  exact asIso (F.map f)

/-- Convert Mathlib's standard continuous-map homotopy, whose parameter is
`unitInterval × X`, to the categorical cylinder convention `X ⊗ TopCat.I`.
The swap and `ULift` conversion are the only content of this adapter. -/
def continuousMapHomotopyCylinder
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.of X ⊗ TopCat.I ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨fun p ↦ H (TopCat.I.homeomorph p.2, p.1),
    H.continuous.comp
      ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst)⟩

@[simp] theorem continuousMapHomotopyCylinder_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.ι₀ ≫ continuousMapHomotopyCylinder H = TopCat.ofHom f := by
  ext x
  change H (0, x) = f x
  simp

@[simp] theorem continuousMapHomotopyCylinder_one
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.ι₁ ≫ continuousMapHomotopyCylinder H = TopCat.ofHom g := by
  ext x
  change H (1, x) = g x
  simp

/-- A standard Mathlib homotopy equivalence induces an isomorphism on ordinary
singular homology. -/
noncomputable def singularHomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    SingularHomology n (TopCat.of X) ≅ SingularHomology n (TopCat.of Y) :=
  singularHomologyIsoOfTopCatHomotopyEquivalence
    (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    (continuousMapHomotopyCylinder (Classical.choice e.left_inv))
    (continuousMapHomotopyCylinder_zero (Classical.choice e.left_inv))
    (continuousMapHomotopyCylinder_one (Classical.choice e.left_inv))
    (continuousMapHomotopyCylinder (Classical.choice e.right_inv))
    (continuousMapHomotopyCylinder_zero (Classical.choice e.right_inv))
    (continuousMapHomotopyCylinder_one (Classical.choice e.right_inv)) n

theorem singularHomologyIsoOfHomotopyEquiv_hom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (singularHomologyIsoOfHomotopyEquiv e n).hom =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom e.toFun) := by
  rfl

/-- Every contractible space has the singular homology of a point. -/
noncomputable def contractibleHomologyIsoPoint
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) :
    SingularHomology n (TopCat.of X) ≅ SingularHomology n Point :=
  singularHomologyIsoOfHomotopyEquiv
    (Classical.choice (ContractibleSpace.hequiv_unit X)) n

/-- The zeroth singular homology of every contractible space is `ℤ`. -/
noncomputable def contractibleH0IsoInt
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    SingularHomology 0 (TopCat.of X) ≅ AddCommGrpCat.of ℤ :=
  contractibleHomologyIsoPoint X 0 ≪≫ pointH0IsoInt

/-- The positive-degree singular homology of every contractible space
vanishes. -/
theorem contractibleHigherHomology_isZero
    (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : IsZero (SingularHomology n (TopCat.of X)) :=
  (pointHigherHomology_isZero n hn).of_iso (contractibleHomologyIsoPoint X n)

/-- The unit interval is contractible by convexity. -/
instance unitIntervalContractibleSpace : ContractibleSpace unitInterval :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩

/-- Concrete computation of the zeroth singular homology of the interval. -/
noncomputable def intervalH0IsoInt :
    SingularHomology 0 (TopCat.of unitInterval) ≅ AddCommGrpCat.of ℤ :=
  contractibleH0IsoInt unitInterval

/-- The exhibited nonzero zeroth-homology class of the interval. -/
noncomputable def intervalH0Generator :
    SingularHomology 0 (TopCat.of unitInterval) :=
  intervalH0IsoInt.inv 1

@[simp] theorem intervalH0IsoInt_hom_generator :
    intervalH0IsoInt.hom intervalH0Generator = 1 := by
  simp [intervalH0Generator]

/-- Anti-vacuity witness: the computed interval theory is not the zero theory. -/
theorem intervalH0Generator_ne_zero : intervalH0Generator ≠ 0 := by
  intro h
  have hgen := intervalH0IsoInt_hom_generator
  rw [h, map_zero] at hgen
  exact zero_ne_one hgen

/-- Concrete computation: the interval has zero singular homology in every
positive degree. -/
theorem intervalHigherHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularHomology n (TopCat.of unitInterval)) :=
  contractibleHigherHomology_isZero unitInterval n hn

/-! ### The relative fundamental class of the interval -/

/-- The two endpoints of the unit interval. -/
def intervalBoundary : Set unitInterval := {0, 1}

/-- Boolean coordinates on the two endpoints. -/
def boolEquivIntervalBoundary : Bool ≃ intervalBoundary where
  toFun b := if b then ⟨1, by simp [intervalBoundary]⟩
    else ⟨0, by simp [intervalBoundary]⟩
  invFun x := x.1 = 1
  left_inv b := by cases b <;> simp
  right_inv x := by
    rcases x.2 with (h | h)
    · apply Subtype.ext
      simp [h]
    · have hx : x.1 = 1 := by simpa using h
      apply Subtype.ext
      simp [hx]

noncomputable instance intervalBoundaryFintype : Fintype intervalBoundary :=
  Fintype.ofEquiv Bool boolEquivIntervalBoundary

/-- The endpoint coordinates are a homeomorphism (both sides are discrete). -/
def boolHomeomorphIntervalBoundary : Bool ≃ₜ intervalBoundary where
  toEquiv := boolEquivIntervalBoundary
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- Degree-zero coordinates on the endpoint subspace, indexed by `Bool`. -/
noncomputable def intervalBoundaryH0Iso :
    SingularHomology 0 (TopCat.of intervalBoundary) ≅
      ∐ fun _ : Bool ↦ AddCommGrpCat.of ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 0).obj
      (AddCommGrpCat.of ℤ)).mapIso
        (TopCat.isoOfHomeo boolHomeomorphIntervalBoundary.symm) ≪≫
    directDiscreteH0Iso AddCommGrpCat (AddCommGrpCat.of ℤ) Bool

/-- Use the actual collapse `I → *` as the coordinate map on interval `H₀`. -/
noncomputable def intervalH0CollapseIso :
    SingularHomology 0 (TopCat.of unitInterval) ≅
      ∐ fun _ : Unit ↦ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv
      (Classical.choice (ContractibleSpace.hequiv_unit unitInterval)) 0 ≪≫
    directDiscreteH0Iso AddCommGrpCat (AddCommGrpCat.of ℤ) Unit

set_option maxHeartbeats 2000000

/-- In the natural coordinates, inclusion of the two endpoints into the
interval is the codiagonal. This is the concrete use of the direct discrete
`H₀` naturality interface. -/
theorem intervalBoundaryH0Inclusion_is_codiagonal :
    intervalBoundaryH0Iso.inv ≫
        HomologicalComplex.homologyMap
          (singularSubspaceMap intervalBoundary) 0 ≫
        intervalH0CollapseIso.hom ≫
        (Limits.coproductUniqueIso
          (fun _ : Unit ↦ AddCommGrpCat.of ℤ)).hom =
      Limits.Sigma.desc (fun _ : Bool ↦ 𝟙 (AddCommGrpCat.of ℤ)) := by
  rw [intervalH0CollapseIso, Iso.trans_hom,
    singularHomologyIsoOfHomotopyEquiv_hom]
  rw [intervalBoundaryH0Iso, Iso.trans_inv]
  let e := Classical.choice (ContractibleSpace.hequiv_unit unitInterval)
  change (directDiscreteH0Iso AddCommGrpCat (AddCommGrpCat.of ℤ) Bool).inv ≫
      HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.isoOfHomeo boolHomeomorphIntervalBoundary.symm).inv) 0 ≫
      HomologicalComplex.homologyMap (singularSubspaceMap intervalBoundary) 0 ≫
      HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.ofHom e.toFun)) 0 ≫
      (directDiscreteH0Iso AddCommGrpCat (AddCommGrpCat.of ℤ) Unit).hom ≫
      (Limits.coproductUniqueIso
        (fun _ : Unit ↦ AddCommGrpCat.of ℤ)).hom =
      Limits.Sigma.desc (fun _ : Bool ↦ 𝟙 (AddCommGrpCat.of ℤ))
  slice_lhs 2 3 => rw [← HomologicalComplex.homologyMap_comp]
  slice_lhs 2 3 => rw [← HomologicalComplex.homologyMap_comp]
  have htop :
      (TopCat.isoOfHomeo boolHomeomorphIntervalBoundary.symm).inv ≫
          subspaceInclusion intervalBoundary ≫ TopCat.ofHom e.toFun =
        boolCollapse := by
    ext b
  have hchain :
      ((((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.isoOfHomeo boolHomeomorphIntervalBoundary.symm).inv ≫
        singularSubspaceMap intervalBoundary) ≫
        ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.ofHom e.toFun)) =
      ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map boolCollapse := by
    dsimp only [singularSubspaceMap]
    rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, htop]
  rw [hchain]
  exact directDiscreteH0Iso_boolCollapse_codiagonal
    AddCommGrpCat (AddCommGrpCat.of ℤ)

abbrev IntGroup := AddCommGrpCat.of ℤ
abbrev BoolIntCoproduct := ∐ fun _ : Bool ↦ IntGroup

/-- The algebraic codiagonal on two integer summands. -/
noncomputable def boolIntCodiagonal : BoolIntCoproduct ⟶ IntGroup :=
  Limits.Sigma.desc (fun _ : Bool ↦ 𝟙 IntGroup)

/-- The oriented difference of the two endpoint basis vectors. -/
noncomputable def boolIntDifference : IntGroup ⟶ BoolIntCoproduct :=
  Limits.Sigma.ι (fun _ : Bool ↦ IntGroup) false -
    Limits.Sigma.ι (fun _ : Bool ↦ IntGroup) true

@[simp] theorem boolIntDifference_codiagonal :
    boolIntDifference ≫ boolIntCodiagonal = 0 := by
  rw [boolIntDifference, Preadditive.sub_comp]
  rw [boolIntCodiagonal]
  rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, sub_self]

theorem boolIntDifference_factor_unique
    (s : Fork boolIntCodiagonal 0) (m : s.pt ⟶ IntGroup)
    (hm : m ≫ boolIntDifference = s.ι) :
    m = s.ι ≫ Limits.Sigma.π (fun _ : Bool ↦ IntGroup) false := by
  have h := congrArg
    (fun f ↦ f ≫ Limits.Sigma.π (fun _ : Bool ↦ IntGroup) false) hm
  dsimp only at h
  rw [Category.assoc, boolIntDifference, Preadditive.sub_comp] at h
  simp only [Limits.Sigma.ι_π_eq_id,
    Limits.Sigma.ι_π_of_ne (f := fun _ : Bool ↦ IntGroup)
      (by decide : true ≠ false), sub_zero, Category.comp_id] at h
  exact h

/-- The difference map exhibits `ℤ` as the kernel of the codiagonal. -/
noncomputable def boolIntDifferenceIsKernel :
    IsLimit (KernelFork.ofι boolIntDifference boolIntDifference_codiagonal) :=
  Fork.IsLimit.mk _
    (fun s ↦ s.ι ≫ Limits.Sigma.π (fun _ : Bool ↦ IntGroup) false)
    (fun s ↦ by
      change (s.ι ≫ Limits.Sigma.π
        (fun _ : Bool ↦ IntGroup) false) ≫ boolIntDifference = s.ι
      let f := fun _ : Bool ↦ IntGroup
      have htotal :
          (∑ j : Bool, Limits.Sigma.π f j ≫ Limits.Sigma.ι f j) =
            𝟙 BoolIntCoproduct := by
        apply Limits.Sigma.hom_ext
        intro b
        rw [Preadditive.comp_sum, Fintype.sum_bool]
        cases b
        · rw [← Category.assoc, Limits.Sigma.ι_π_of_ne f (by decide),
            zero_comp, ← Category.assoc, Limits.Sigma.ι_π_eq_id f false,
            Category.id_comp, zero_add, Category.comp_id]
        · rw [← Category.assoc, Limits.Sigma.ι_π_eq_id f true,
            Category.id_comp, ← Category.assoc,
            Limits.Sigma.ι_π_of_ne f (by decide), zero_comp, add_zero,
            Category.comp_id]
      have hs : s.ι ≫ Limits.Sigma.π (fun _ : Bool ↦ IntGroup) true =
          -(s.ι ≫ Limits.Sigma.π (fun _ : Bool ↦ IntGroup) false) := by
        have hz : s.ι ≫ boolIntCodiagonal = 0 := KernelFork.condition s
        have hsum : s.ι ≫ Limits.Sigma.π
              (fun _ : Bool ↦ IntGroup) true +
            s.ι ≫ Limits.Sigma.π
              (fun _ : Bool ↦ IntGroup) false = 0 := by
          rw [← Category.comp_id s.ι, ← htotal, Preadditive.comp_sum,
            Fintype.sum_bool] at hz
          simp only [Preadditive.add_comp, Category.assoc,
            boolIntCodiagonal, Limits.Sigma.ι_desc] at hz
          simpa only [add_comm] using hz
        exact eq_neg_of_add_eq_zero_left hsum
      rw [boolIntDifference, Preadditive.comp_sub]
      calc
        (s.ι ≫ Limits.Sigma.π f false) ≫ Limits.Sigma.ι f false -
            (s.ι ≫ Limits.Sigma.π f false) ≫ Limits.Sigma.ι f true =
          (s.ι ≫ Limits.Sigma.π f false) ≫ Limits.Sigma.ι f false +
            (s.ι ≫ Limits.Sigma.π f true) ≫ Limits.Sigma.ι f true := by
              rw [show s.ι ≫ Limits.Sigma.π f true =
                -(s.ι ≫ Limits.Sigma.π f false) by simpa [f] using hs]
              simp only [sub_eq_add_neg, Preadditive.neg_comp]
        _ = s.ι ≫ (∑ j : Bool,
              Limits.Sigma.π f j ≫ Limits.Sigma.ι f j) := by
          rw [Fintype.sum_bool, Preadditive.comp_add]
          simp only [Category.assoc, add_comm]
        _ = s.ι := by rw [htotal, Category.comp_id])
    (fun s m hm ↦ by
      change m ≫ boolIntDifference = s.ι at hm
      exact boolIntDifference_factor_unique s m hm)

/-- Canonical identification of the codiagonal kernel with one copy of
the integers. -/
noncomputable def boolIntCodiagonalKernelIso :
    kernel boolIntCodiagonal ≅ IntGroup :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    boolIntDifferenceIsKernel

/-- The endpoint inclusion on degree-zero homology. -/
noncomputable def intervalEndpointH0Map :
    SingularHomology 0 (TopCat.of intervalBoundary) ⟶
      SingularHomology 0 (TopCat.of unitInterval) :=
  HomologicalComplex.homologyMap
    (singularSubspaceMap intervalBoundary) 0

/-- Coordinates on the target of the endpoint map, using collapse to a point. -/
noncomputable def intervalH0CollapseToIntIso :
    SingularHomology 0 (TopCat.of unitInterval) ≅ IntGroup :=
  intervalH0CollapseIso ≪≫
    Limits.coproductUniqueIso (fun _ : Unit ↦ IntGroup)

theorem intervalEndpointH0Map_coordinates :
    intervalEndpointH0Map ≫ intervalH0CollapseToIntIso.hom =
      intervalBoundaryH0Iso.hom ≫ boolIntCodiagonal := by
  apply (cancel_epi intervalBoundaryH0Iso.inv).1
  simpa [intervalEndpointH0Map, intervalH0CollapseToIntIso, Category.assoc] using
    intervalBoundaryH0Inclusion_is_codiagonal

/-- Transport the endpoint-map kernel to the explicitly computed codiagonal
kernel. -/
noncomputable def intervalEndpointKernelIsoCodiagonalKernel :
  kernel intervalEndpointH0Map ≅ kernel boolIntCodiagonal :=
  kernel.mapIso (f := intervalEndpointH0Map) boolIntCodiagonal intervalBoundaryH0Iso
    intervalH0CollapseToIntIso intervalEndpointH0Map_coordinates

/-- The interval connecting map is injective because the preceding absolute
degree-one homology group vanishes. -/
noncomputable instance intervalPairConnecting_mono :
    Mono (singularPairConnecting intervalBoundary 0) := by
  apply (singularPairHomology_exact_relative intervalBoundary 0).mono_g
  exact (intervalHigherHomology_isZero 1 (by decide)).eq_of_src _ _

/-- Exactness identifies relative `H₁(I,∂I)` with the kernel of the endpoint
map on `H₀`. -/
noncomputable def intervalRelativeH1IsoEndpointKernel :
    (RelativeSingularChains intervalBoundary).homology 1 ≅
      kernel intervalEndpointH0Map :=
  IsLimit.conePointUniqueUpToIso
    (singularPairHomology_exact_subspace intervalBoundary 0).fIsKernel
    (limit.isLimit _)

/-- The first relative singular homology of the interval modulo its endpoints
is one copy of the integers. -/
noncomputable def intervalBoundaryRelativeH1IsoInt :
    (RelativeSingularChains intervalBoundary).homology 1 ≅ IntGroup :=
  intervalRelativeH1IsoEndpointKernel ≪≫
    intervalEndpointKernelIsoCodiagonalKernel ≪≫
    boolIntCodiagonalKernelIso

/-- The oriented relative fundamental class of the interval. -/
noncomputable def intervalBoundaryRelativeH1Generator :
    (RelativeSingularChains intervalBoundary).homology 1 :=
  intervalBoundaryRelativeH1IsoInt.inv 1

@[simp] theorem intervalBoundaryRelativeH1IsoInt_generator :
    intervalBoundaryRelativeH1IsoInt.hom
      intervalBoundaryRelativeH1Generator = 1 := by
  simp [intervalBoundaryRelativeH1Generator]

/-- Anti-vacuity: the relative fundamental class maps to `1`, hence is
nonzero. -/
theorem intervalBoundaryRelativeH1Generator_ne_zero :
    intervalBoundaryRelativeH1Generator ≠ 0 := by
  intro h
  have hgen := intervalBoundaryRelativeH1IsoInt_generator
  rw [h, map_zero] at hgen
  exact zero_ne_one hgen

/-- The degree-one boundary in the one-vertex, one-edge CW model of `S¹`.
Both endpoints of the oriented edge are the unique vertex, hence the boundary
is zero. -/
def circleCellularBoundaryOne : ℤ →+ ℤ := 0

/-- The full cellular chain complex of the one-vertex, one-edge CW circle:
`ℤ` in degrees zero and one, zero elsewhere, with zero differential. -/
noncomputable def circleCellularChainComplex : ChainComplex AddCommGrpCat ℕ :=
  ChainComplex.of
    (fun n ↦ if n = 0 ∨ n = 1 then AddCommGrpCat.of ℤ else 0)
    (fun _ ↦ 0) (fun _ ↦ by cat_disch)

@[simp] theorem circleCellularChainComplex_X_zero :
    circleCellularChainComplex.X 0 = AddCommGrpCat.of ℤ := by
  simp [circleCellularChainComplex]

@[simp] theorem circleCellularChainComplex_X_one :
    circleCellularChainComplex.X 1 = AddCommGrpCat.of ℤ := by
  simp [circleCellularChainComplex]

theorem circleCellularChainComplex_isZero_X (n : ℕ) (hn : 2 ≤ n) :
    IsZero (circleCellularChainComplex.X n) := by
  change IsZero (if n = 0 ∨ n = 1 then AddCommGrpCat.of ℤ else 0)
  rw [if_neg]
  · exact isZero_zero AddCommGrpCat
  · omega

@[simp] theorem circleCellularChainComplex_d (n : ℕ) :
    circleCellularChainComplex.d (n + 1) n = 0 := by
  simp [circleCellularChainComplex]
  rfl

theorem circleCellularChainComplex_d_all (i j : ℕ) :
    circleCellularChainComplex.d i j = 0 := by
  by_cases h : i = j + 1
  · subst i
    exact circleCellularChainComplex_d j
  · exact circleCellularChainComplex.shape i j (fun hij ↦ h hij.symm)

/-- Since all cellular differentials vanish, homology in every degree is
canonically isomorphic to the chain object in that degree. -/
noncomputable def circleCellularModelHomologyIsoX (n : ℕ) :
    circleCellularChainComplex.homology n ≅ circleCellularChainComplex.X n :=
  (circleCellularChainComplex.isoHomologyπ
      ((ComplexShape.down ℕ).prev n) n rfl
      (circleCellularChainComplex_d_all _ _)).symm ≪≫
    circleCellularChainComplex.iCyclesIso
      n ((ComplexShape.down ℕ).next n) rfl
      (circleCellularChainComplex_d_all _ _)

/-- The zeroth homology of the cellular circle model is `ℤ`. -/
noncomputable def circleCellularModelH0IsoInt :
    circleCellularChainComplex.homology 0 ≅ AddCommGrpCat.of ℤ :=
  circleCellularModelHomologyIsoX 0 ≪≫ eqToIso circleCellularChainComplex_X_zero

/-- The first homology of the cellular circle model is `ℤ`. -/
noncomputable def circleCellularModelH1IsoInt :
    circleCellularChainComplex.homology 1 ≅ AddCommGrpCat.of ℤ :=
  circleCellularModelHomologyIsoX 1 ≪≫ eqToIso circleCellularChainComplex_X_one

/-- The cellular circle model has zero homology above degree one. -/
theorem circleCellularModelHigherHomology_isZero (n : ℕ) (hn : 2 ≤ n) :
    IsZero (circleCellularChainComplex.homology n) :=
  (circleCellularChainComplex_isZero_X n hn).of_iso
    (circleCellularModelHomologyIsoX n)

/-- Equivalently, the cellular circle model vanishes in every degree other
than zero and one. -/
theorem circleCellularModelHomology_isZero_of_ne_zero_one
    (n : ℕ) (h₀ : n ≠ 0) (h₁ : n ≠ 1) :
    IsZero (circleCellularChainComplex.homology n) :=
  circleCellularModelHigherHomology_isZero n (by omega)

/-- The oriented one-cell transported into the first homology of the packaged
cellular complex. -/
noncomputable def circleCellularModelH1Generator :
    circleCellularChainComplex.homology 1 :=
  circleCellularModelH1IsoInt.inv 1

@[simp] theorem circleCellularModelH1IsoInt_hom_generator :
    circleCellularModelH1IsoInt.hom circleCellularModelH1Generator = 1 := by
  simp [circleCellularModelH1Generator]

/-- Anti-vacuity witness for the packaged complex's computed homology. -/
theorem circleCellularModelH1Generator_ne_zero :
    circleCellularModelH1Generator ≠ 0 := by
  intro h
  have hgen := circleCellularModelH1IsoInt_hom_generator
  rw [h, map_zero] at hgen
  exact zero_ne_one hgen

/-- The oriented one-cell as a concrete degree-one chain. -/
def circleCellularOneChain : circleCellularChainComplex.X 1 := by
  change ℤ
  exact 1

/-- Anti-vacuity witness for the full complex: its oriented one-cell is not the
zero chain. -/
theorem circleCellularOneChain_ne_zero : circleCellularOneChain ≠ 0 :=
  by
    change (1 : ℤ) ≠ 0
    exact one_ne_zero

@[simp] theorem circleCellularBoundaryOne_apply (z : ℤ) :
    circleCellularBoundaryOne z = 0 := rfl

/-- Every cellular one-chain in the standard circle model is a cycle. -/
theorem circleCellularBoundaryOne_ker : circleCellularBoundaryOne.ker = ⊤ := by
  ext z
  simp [circleCellularBoundaryOne]

/-- There are no degree-two cells in the standard circle CW structure, so the
subgroup of degree-one cellular boundaries is zero. -/
def circleCellularBoundariesOne : AddSubgroup ℤ := ⊥

/-- First homology of the standard one-vertex, one-edge cellular circle model:
cycles modulo boundaries. -/
abbrev CircleCellularH1 := ℤ ⧸ circleCellularBoundariesOne

/-- The quotient computation `H₁(CW(S¹)) ≃ ℤ` as an additive-group
isomorphism. -/
def circleCellularH1EquivInt : CircleCellularH1 ≃+ ℤ where
  toFun := QuotientAddGroup.lift circleCellularBoundariesOne
    (AddMonoidHom.id ℤ) (by simp [circleCellularBoundariesOne])
  invFun := QuotientAddGroup.mk' circleCellularBoundariesOne
  left_inv q := by
    induction q using Quotient.inductionOn
    rfl
  right_inv _ := rfl
  map_add' x y := by simp

/-- The oriented one-cell gives the canonical degree-one class. -/
def circleCellularGenerator : CircleCellularH1 :=
  QuotientAddGroup.mk' circleCellularBoundariesOne 1

/-- The exhibited generator is sent to the independently known integer `1`. -/
@[simp] theorem circleCellularH1EquivInt_generator :
    circleCellularH1EquivInt circleCellularGenerator = 1 := by
  rfl

/-- Anti-vacuity witness: the computed first homology of the circle model is
not the trivial group. -/
theorem circleCellularGenerator_ne_zero : circleCellularGenerator ≠ 0 := by
  intro h
  have := congrArg circleCellularH1EquivInt h
  exact one_ne_zero this

/-- Consequently the standard cellular circle model has a genuinely
nontrivial first homology group. -/
theorem circleCellularH1_nontrivial : Nontrivial CircleCellularH1 := by
  exact ⟨⟨circleCellularGenerator, 0, circleCellularGenerator_ne_zero⟩⟩

end ConstructionTargets.SingularHomologyConcrete

#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularBoundaryOne_ker
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularH1EquivInt
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularH1EquivInt_generator
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularGenerator_ne_zero
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularH1_nontrivial
#print axioms ConstructionTargets.SingularHomologyConcrete.pointH0IsoInt
#print axioms ConstructionTargets.SingularHomologyConcrete.pointH0IsoInt_hom_generator
#print axioms ConstructionTargets.SingularHomologyConcrete.pointH0Generator_ne_zero
#print axioms ConstructionTargets.SingularHomologyConcrete.pointHigherHomology_isZero
#print axioms ConstructionTargets.SingularHomologyConcrete.topCatHomotopyToSSet
#print axioms ConstructionTargets.SingularHomologyConcrete.singularHomology_map_eq_of_topCatHomotopy
#print axioms ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfTopCatHomotopyEquivalence
#print axioms ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
#print axioms ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv_hom
#print axioms ConstructionTargets.SingularHomologyConcrete.contractibleHomologyIsoPoint
#print axioms ConstructionTargets.SingularHomologyConcrete.contractibleH0IsoInt
#print axioms ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
#print axioms ConstructionTargets.SingularHomologyConcrete.intervalH0IsoInt
#print axioms ConstructionTargets.SingularHomologyConcrete.intervalH0IsoInt_hom_generator
#print axioms ConstructionTargets.SingularHomologyConcrete.intervalH0Generator_ne_zero
#print axioms ConstructionTargets.SingularHomologyConcrete.intervalHigherHomology_isZero
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularChainComplex_isZero_X
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularChainComplex_d
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularOneChain_ne_zero
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularModelH0IsoInt
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularModelH1IsoInt
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularModelHomology_isZero_of_ne_zero_one
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularModelH1IsoInt_hom_generator
#print axioms ConstructionTargets.SingularHomologyConcrete.circleCellularModelH1Generator_ne_zero
#print axioms ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex_differential_restricts
#print axioms ConstructionTargets.SingularHomologyConcrete.relativeSingularChainsIsoCokernelSubspaceMap
#print axioms ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularChains_isZero
#print axioms ConstructionTargets.SingularHomologyConcrete.relativeEmptyIsoAbsolute
#print axioms ConstructionTargets.SingularHomologyConcrete.falsePairRelativeDegreeZeroWeight_trueClass
#print axioms ConstructionTargets.SingularHomologyConcrete.falsePairRelativeTrueClass_ne_zero
#print axioms ConstructionTargets.SingularHomologyConcrete.subspaceInclusion_singularSimplex_injective
#print axioms ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap_mono
#print axioms ConstructionTargets.SingularHomologyConcrete.singularPairShortComplex_shortExact
#print axioms ConstructionTargets.SingularHomologyConcrete.singularPairConnecting
#print axioms ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_subspace
#print axioms ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_absolute
#print axioms ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_relative
#print axioms ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero
#print axioms ConstructionTargets.SingularHomologyConcrete.selfPairPointLES_generator_evaluates_to_one
#print axioms ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
#print axioms ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso_pointInclusion
#print axioms ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso_naturality
#print axioms ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso_boolCollapse_codiagonal
#print axioms ConstructionTargets.SingularHomologyConcrete.intervalBoundaryH0Inclusion_is_codiagonal
#print axioms ConstructionTargets.SingularHomologyConcrete.boolIntDifferenceIsKernel
#print axioms ConstructionTargets.SingularHomologyConcrete.boolIntDifference_factor_unique
#print axioms ConstructionTargets.SingularHomologyConcrete.intervalRelativeH1IsoEndpointKernel
#print axioms ConstructionTargets.SingularHomologyConcrete.intervalBoundaryRelativeH1IsoInt
#print axioms ConstructionTargets.SingularHomologyConcrete.intervalBoundaryRelativeH1IsoInt_generator
#print axioms ConstructionTargets.SingularHomologyConcrete.intervalBoundaryRelativeH1Generator_ne_zero
