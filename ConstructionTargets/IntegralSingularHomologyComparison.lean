import ConstructionTargets.T02A06SphereOne
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Integral singular homology across the two canonical coefficient categories

The forgetful equivalence from `ℤ`-modules to additive commutative groups
preserves the coproducts used to form singular chains and the kernels and
cokernels used to form homology.  This file packages the resulting comparison
so computations made in `AddCommGrpCat` can be consumed by statements phrased
in `ModuleCat ℤ`.
-/

noncomputable section

namespace ConstructionTargets.IntegralSingularHomologyComparison

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive
open ConstructionTargets.SingularSubdivision

abbrev forgetIntModules : ModuleCat ℤ ⥤ AddCommGrpCat :=
  forget₂ (ModuleCat ℤ) AddCommGrpCat

private abbrev moduleChains (X : TopCat) :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X

private abbrev groupChains (X : TopCat) :=
  ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (forgetIntModules.obj (ModuleCat.of ℤ ℤ))).obj X

/-- Degreewise, forgetting the module structure on integral singular chains
is the canonical comparison between the two coproduct constructions. -/
noncomputable def singularChainsComparisonXIso (X : TopCat) (n : ℕ) :
    ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (moduleChains X)).X n ≅ (groupChains X).X n := by
  exact PreservesCoproduct.iso forgetIntModules
    (fun _ : SingularSimplex X n => ModuleCat.of ℤ ℤ)

/-- Forgetting integral-module singular chains gives the usual singular chain
complex in additive commutative groups. -/
noncomputable def singularChainsComparison (X : TopCat) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (moduleChains X) ≅ groupChains X :=
  HomologicalComplex.Hom.isoOfComponents (singularChainsComparisonXIso X) (by
    rintro i j hij
    obtain rfl : i = j + 1 := hij.symm
    rw [← cancel_epi (singularChainsComparisonXIso X (j + 1)).inv]
    simp only [Iso.inv_hom_id_assoc]
    apply Limits.Sigma.hom_ext
    intro s
    dsimp only [singularChainsComparisonXIso]
    rw [PreservesCoproduct.inv_hom]
    erw [Limits.ι_comp_sigmaComparison_assoc]
    simp only [Functor.mapHomologicalComplex_obj_d]
    change _ =
      (forgetIntModules.map (Limits.Sigma.ι
          (fun _ : SingularSimplex X (j + 1) => ModuleCat.of ℤ ℤ) s) ≫
        forgetIntModules.map ((moduleChains X).d (j + 1) j)) ≫
          (singularChainsComparisonXIso X j).hom
    rw [← forgetIntModules.map_comp]
    have hmodule :
        Limits.Sigma.ι
            (fun _ : SingularSimplex X (j + 1) => ModuleCat.of ℤ ℤ) s ≫
            (moduleChains X).d (j + 1) j =
          ∑ a : Fin (j + 2), (-1 : ℤ) ^ (a : ℕ) •
            Limits.Sigma.ι (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ a s) := by
      dsimp [moduleChains, AlgebraicTopology.singularChainComplexFunctor,
        AlgebraicTopology.SSet.singularChainComplexFunctor]
      rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
      unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
      calc
        _ = ∑ a : Fin (j + 2), Limits.Sigma.ι
              (fun _ : SingularSimplex X (j + 1) => ModuleCat.of ℤ ℤ) s ≫
            ((-1 : ℤ) ^ (a : ℕ) •
              ((((SimplicialObject.whiskering Type (ModuleCat ℤ)).obj
                (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ))).obj
                  (TopCat.toSSet.obj X)).δ a)) := by
          simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte]
            using Preadditive.comp_sum
              (Finset.univ : Finset (Fin (j + 2)))
              (Limits.Sigma.ι
                (fun _ : SingularSimplex X (j + 1) => ModuleCat.of ℤ ℤ) s)
              (fun a => (-1 : ℤ) ^ (a : ℕ) •
                ((((SimplicialObject.whiskering Type (ModuleCat ℤ)).obj
                  (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ))).obj
                    (TopCat.toSSet.obj X)).δ a))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a _
          calc
            _ = (-1 : ℤ) ^ (a : ℕ) •
                (Limits.Sigma.ι
                  (fun _ : SingularSimplex X (j + 1) => ModuleCat.of ℤ ℤ) s ≫
                  ((((SimplicialObject.whiskering Type (ModuleCat ℤ)).obj
                    (CategoryTheory.Limits.sigmaConst.obj
                      (ModuleCat.of ℤ ℤ))).obj
                        (TopCat.toSSet.obj X)).δ a)) := by
              exact Preadditive.comp_zsmul _ _ _
            _ = _ := by
              congr 1
              dsimp [SimplicialObject.δ, SimplicialObject.whiskering,
                CategoryTheory.Limits.sigmaConst]
              rw [Limits.Sigma.ι_comp_map']
              simp
    have hgroup :
        Limits.Sigma.ι
            (fun _ : SingularSimplex X (j + 1) =>
              forgetIntModules.obj (ModuleCat.of ℤ ℤ)) s ≫
            (groupChains X).d (j + 1) j =
          ∑ a : Fin (j + 2), (-1 : ℤ) ^ (a : ℕ) •
            Limits.Sigma.ι (fun _ : SingularSimplex X j =>
              forgetIntModules.obj (ModuleCat.of ℤ ℤ))
              ((TopCat.toSSet.obj X).δ a s) := by
      exact singularGenerator_boundary X j s
    rw [hmodule, hgroup]
    have hmap : forgetIntModules.map
          (∑ a : Fin (j + 2), (-1 : ℤ) ^ (a : ℕ) •
            Limits.Sigma.ι (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ a s)) =
        ∑ a : Fin (j + 2), forgetIntModules.map
          ((-1 : ℤ) ^ (a : ℕ) •
            Limits.Sigma.ι (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ a s)) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
        forgetIntModules.map_sum
          (fun a : Fin (j + 2) => (-1 : ℤ) ^ (a : ℕ) •
            Limits.Sigma.ι (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ a s))
          (Finset.univ : Finset (Fin (j + 2)))
    erw [hmap]
    have hcomp :
        (∑ a : Fin (j + 2), forgetIntModules.map
          ((-1 : ℤ) ^ (a : ℕ) •
            Limits.Sigma.ι (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ a s))) ≫
            (singularChainsComparisonXIso X j).hom =
          ∑ a : Fin (j + 2), forgetIntModules.map
            ((-1 : ℤ) ^ (a : ℕ) •
              Limits.Sigma.ι (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.obj X).δ a s)) ≫
              (singularChainsComparisonXIso X j).hom := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
        Preadditive.sum_comp (Finset.univ : Finset (Fin (j + 2)))
          (fun a => forgetIntModules.map
            ((-1 : ℤ) ^ (a : ℕ) •
              Limits.Sigma.ι (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.obj X).δ a s)))
          (singularChainsComparisonXIso X j).hom
    erw [hcomp]
    apply Finset.sum_congr rfl
    intro a _
    rw [Functor.map_zsmul, Preadditive.zsmul_comp]
    congr 1
    dsimp only [singularChainsComparisonXIso]
    have hhom : (PreservesCoproduct.iso forgetIntModules
        (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)).hom =
          inv (sigmaComparison forgetIntModules
            (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)) := by
      symm
      apply IsIso.inv_eq_of_hom_inv_id
      simpa only [PreservesCoproduct.inv_hom] using
        (PreservesCoproduct.iso forgetIntModules
          (fun _ : SingularSimplex X j => ModuleCat.of ℤ ℤ)).inv_hom_id
    rw [hhom]
    exact (Limits.map_ι_comp_inv_sigmaComparison _ _ _).symm)

/-- The chain comparison commutes with the singular-chain map induced by a
continuous map.  This is proved on the canonical singular-simplex generators;
in particular it is not an objectwise comparison promoted to naturality by an
assumption. -/
theorem singularChainsComparison_naturality {X Y : TopCat} (f : X ⟶ Y) :
    ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f)) ≫
        (singularChainsComparison Y).hom =
      (singularChainsComparison X).hom ≫
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_epi (singularChainsComparisonXIso X n).inv).1
  simp only [HomologicalComplex.comp_f]
  dsimp [singularChainsComparison]
  rw [Iso.inv_hom_id_assoc]
  apply Limits.Sigma.hom_ext
  intro s
  dsimp only [singularChainsComparison, singularChainsComparisonXIso]
  rw [PreservesCoproduct.inv_hom]
  erw [Limits.ι_comp_sigmaComparison_assoc]
  have hmodule :
      Limits.Sigma.ι (fun _ : SingularSimplex X n => ModuleCat.of ℤ ℤ) s ≫
          ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map f).f n) =
        Limits.Sigma.ι (fun _ : SingularSimplex Y n => ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map f).app _ s) := by
    dsimp [AlgebraicTopology.singularChainComplexFunctor,
      AlgebraicTopology.SSet.singularChainComplexFunctor]
    rw [Limits.Sigma.ι_comp_map']
    simp
  change forgetIntModules.map
      (Limits.Sigma.ι (fun _ : SingularSimplex X n => ModuleCat.of ℤ ℤ) s) ≫
        forgetIntModules.map
          ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map f).f n) ≫
        (PreservesCoproduct.iso forgetIntModules
          (fun _ : SingularSimplex Y n => ModuleCat.of ℤ ℤ)).hom = _
  rw [← forgetIntModules.map_comp_assoc]
  rw [hmodule]
  have hhom : (PreservesCoproduct.iso forgetIntModules
      (fun _ : SingularSimplex Y n => ModuleCat.of ℤ ℤ)).hom =
        inv (sigmaComparison forgetIntModules
          (fun _ : SingularSimplex Y n => ModuleCat.of ℤ ℤ)) := by
    symm
    apply IsIso.inv_eq_of_hom_inv_id
    simpa only [PreservesCoproduct.inv_hom] using
      (PreservesCoproduct.iso forgetIntModules
        (fun _ : SingularSimplex Y n => ModuleCat.of ℤ ℤ)).inv_hom_id
  rw [hhom]
  calc
    _ = Limits.Sigma.ι
        (fun _ : SingularSimplex Y n => forgetIntModules.obj (ModuleCat.of ℤ ℤ))
        ((TopCat.toSSet.map f).app _ s) := by
      exact Limits.map_ι_comp_inv_sigmaComparison
        (G := forgetIntModules)
        (f := fun _ : SingularSimplex Y n => ModuleCat.of ℤ ℤ)
        ((TopCat.toSSet.map f).app _ s)
    _ = _ := by
      dsimp [AlgebraicTopology.singularChainComplexFunctor,
        AlgebraicTopology.SSet.singularChainComplexFunctor]
      symm
      simpa only [Category.id_comp] using Limits.Sigma.ι_comp_map'
        (f := fun _ : SingularSimplex X n => AddCommGrpCat.of ℤ)
        (g := fun _ : SingularSimplex Y n => AddCommGrpCat.of ℤ)
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)))
        (fun _ ↦ 𝟙 (AddCommGrpCat.of ℤ)) s

/-- Integral singular homology in `ModuleCat ℤ`, after forgetting, is the
same object as integral singular homology computed in `AddCommGrpCat`. -/
noncomputable def singularHomologyComparison (X : TopCat) (k : ℕ) :
    forgetIntModules.obj
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
          (ModuleCat.of ℤ ℤ)).obj X) ≅
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
        (AddCommGrpCat.of ℤ)).obj X) := by
  let K := moduleChains X
  exact ((K.sc k).mapHomologyIso forgetIntModules).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat
      (ComplexShape.down ℕ) k).mapIso (singularChainsComparison X)

/-- The homology comparison is natural for every continuous map.  The left
side is the integral-module homology map after forgetting its scalar
structure; the right side is the map computed natively in additive
commutative groups. -/
theorem singularHomologyComparison_naturality {X Y : TopCat} (f : X ⟶ Y)
    (k : ℕ) :
    forgetIntModules.map
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
          (ModuleCat.of ℤ ℤ)).map f) ≫
        (singularHomologyComparison Y k).hom =
      (singularHomologyComparison X k).hom ≫
        (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
          (AddCommGrpCat.of ℤ)).map f) := by
  let φ := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map f
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
    (ComplexShape.down ℕ) k).map φ
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) k
  change forgetIntModules.map (HomologicalComplex.homologyMap φ k) ≫
      ((HomologicalComplex.sc (moduleChains Y) k).mapHomologyIso
        forgetIntModules).inv ≫
      H.map (singularChainsComparison Y).hom =
    (((HomologicalComplex.sc (moduleChains X) k).mapHomologyIso
        forgetIntModules).inv ≫
      H.map (singularChainsComparison X).hom) ≫
      H.map ((((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map f))
  have hφ : ShortComplex.homologyMap ψ =
      HomologicalComplex.homologyMap φ k := rfl
  rw [← hφ]
  have hpres := ShortComplex.mapHomologyIso_inv_naturality ψ forgetIntModules
  change forgetIntModules.map (ShortComplex.homologyMap ψ) ≫
      ((HomologicalComplex.sc (moduleChains Y) k).mapHomologyIso
        forgetIntModules).inv =
    ((HomologicalComplex.sc (moduleChains X) k).mapHomologyIso
        forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        (((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map φ)) k
    at hpres
  change (forgetIntModules.map (ShortComplex.homologyMap ψ) ≫
      ((HomologicalComplex.sc (moduleChains Y) k).mapHomologyIso
        forgetIntModules).inv) ≫ _ = _
  rw [hpres]
  change ((HomologicalComplex.sc (moduleChains X) k).mapHomologyIso
      forgetIntModules).inv ≫
        (H.map (((forgetIntModules.mapHomologicalComplex
              (ComplexShape.down ℕ)).map φ)) ≫
          H.map (singularChainsComparison Y).hom) =
    ((HomologicalComplex.sc (moduleChains X) k).mapHomologyIso
      forgetIntModules).inv ≫
        (H.map (singularChainsComparison X).hom ≫
          H.map ((((AlgebraicTopology.singularChainComplexFunctor
            AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map f)))
  have hinner :
      H.map (((forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map φ)) ≫
          H.map (singularChainsComparison Y).hom =
        H.map (singularChainsComparison X).hom ≫
          H.map ((((AlgebraicTopology.singularChainComplexFunctor
            AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map f)) := by
    rw [← H.map_comp, singularChainsComparison_naturality f, H.map_comp]
  exact congrArg
    (fun z ↦ ((HomologicalComplex.sc (moduleChains X) k).mapHomologyIso
      forgetIntModules).inv ≫ z) hinner

/-- Lift an isomorphism of underlying additive groups uniquely to an
isomorphism of `ℤ`-modules. -/
noncomputable def moduleIsoOfUnderlyingIso {A B : ModuleCat ℤ}
    (e : forgetIntModules.obj A ≅ forgetIntModules.obj B) : A ≅ B :=
  forgetIntModules.preimageIso e

/-- The equivalence with additive commutative groups reflects zero objects. -/
theorem moduleIsZeroOfUnderlyingIsZero {A : ModuleCat ℤ}
    (h : IsZero (forgetIntModules.obj A)) : IsZero A := by
  rw [IsZero.iff_id_eq_zero]
  apply forgetIntModules.map_injective
  rw [forgetIntModules.map_id, forgetIntModules.map_zero]
  exact h.eq_of_src _ _

/-- Transfer an additive-group computation of integral singular homology to
the canonical `ModuleCat ℤ` formulation. -/
noncomputable def singularHomologyModuleIsoOfGroupIso
    (X : TopCat) (k : ℕ) (B : ModuleCat ℤ)
    (e : (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
      (AddCommGrpCat.of ℤ)).obj X) ≅ forgetIntModules.obj B) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).obj X) ≅ B :=
  moduleIsoOfUnderlyingIso (singularHomologyComparison X k ≪≫ e)

/-- Transfer vanishing of additive-group singular homology to the canonical
`ModuleCat ℤ` formulation. -/
theorem singularHomologyModuleIsZeroOfGroupIsZero
    (X : TopCat) (k : ℕ)
    (h : IsZero (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
      (AddCommGrpCat.of ℤ)).obj X)) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).obj X) :=
  moduleIsZeroOfUnderlyingIsZero
    (h.of_iso (singularHomologyComparison X k))

#print axioms singularChainsComparison
#print axioms singularChainsComparison_naturality
#print axioms singularHomologyComparison
#print axioms singularHomologyComparison_naturality
#print axioms singularHomologyModuleIsoOfGroupIso
#print axioms singularHomologyModuleIsZeroOfGroupIsZero

end ConstructionTargets.IntegralSingularHomologyComparison
