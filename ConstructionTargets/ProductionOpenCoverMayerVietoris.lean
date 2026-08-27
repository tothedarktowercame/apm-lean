import ConstructionTargets.BooleanTwoCoverScaffold
import Mathlib.Algebra.Homology.Additive

/-!
# Production open-cover Mayer--Vietoris transport

This file packages the exact categorical transport needed to move the compiled
subcomplex Mayer--Vietoris sequence onto isomorphic production homology
objects, and packages the cover-small/production homology isomorphism in every
degree.  It does not identify the three subcomplex terms with the singular
homology of `U ∩ V`, `U`, and `V`; that naturality comparison remains explicit.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.ProductionOpenCoverMayerVietoris

open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.BooleanTwoCoverScaffold

private abbrev ssetChains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

/-- The canonical additive-functor comparison between homology of a chain
complex biproduct and the biproduct of homology objects. -/
noncomputable def homologyBiprodIso
    (K L : ChainComplex AddCommGrpCat ℕ) (n : ℕ) :
    (K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n := by
  let F := HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) n
  letI : F.Additive := inferInstance
  letI : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod K L

theorem homologyBiprodIso_hom
    (K L : ChainComplex AddCommGrpCat ℕ) (n : ℕ) :
    (homologyBiprodIso K L n).hom =
      biprod.lift
        (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) n)
        (HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) n) := by
  rfl

theorem homologyBiprodIso_inv
    (K L : ChainComplex AddCommGrpCat ℕ) (n : ℕ) :
    (homologyBiprodIso K L n).inv =
      biprod.desc
        (HomologicalComplex.homologyMap (biprod.inl : K ⟶ K ⊞ L) n)
        (HomologicalComplex.homologyMap (biprod.inr : L ⟶ K ⊞ L) n) := by
  rfl

/-- Homology of an ambient range subcomplex as the production singular
homology of its underlying topological subspace. -/
noncomputable def ambientRangeProductionHomologyIso
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ssetChains.obj (ambientSubspaceRange A : SSet)).homology n ≅
      (SingularChains (TopCat.of A)).homology n :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) n).mapIso (ambientSubspaceRangeChainsIso A)

/-- The stored Boolean-cover intersection term as production homology of
`U ∩ V`. -/
noncomputable def booleanIntersectionProductionHomologyIso
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    ((shortComplex U V).X₁).homology n ≅
      (SingularChains (TopCat.of (U ∩ V : Set X))).homology n :=
  (ambientIntersectionRangeHomologyIso U V n).symm ≪≫
    ambientRangeProductionHomologyIso (U ∩ V) n

/-- The stored Boolean-cover middle term as the biproduct of the production
homologies of `U` and `V`. -/
noncomputable def booleanPiecesProductionHomologyIso
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    ((shortComplex U V).X₂).homology n ≅
      (SingularChains (TopCat.of U)).homology n ⊞
        (SingularChains (TopCat.of V)).homology n := by
  dsimp [shortComplex, subcomplexMayerVietorisShortComplex]
  exact (homologyBiprodIso
      (ssetChains.obj (leftRange U : SSet))
      (ssetChains.obj (rightRange V : SSet)) n) ≪≫
    biprod.mapIso
      (ambientRangeProductionHomologyIso U n)
      (ambientRangeProductionHomologyIso V n)

/-- The actual signed pair of inclusion-induced maps from `U ∩ V` into
the two members of the cover. -/
noncomputable def productionIntersectionArrow
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (SingularChains (TopCat.of (U ∩ V : Set X))).homology n ⟶
      (SingularChains (TopCat.of U)).homology n ⊞
        (SingularChains (TopCat.of V)).homology n :=
  biprod.lift
    (HomologicalComplex.homologyMap
      (ssetChains.map (TopCat.toSSet.map
        (topologicalSubspaceInclusion (Set.inter_subset_left)))) n)
    (-HomologicalComplex.homologyMap
      (ssetChains.map (TopCat.toSSet.map
        (topologicalSubspaceInclusion (Set.inter_subset_right)))) n)


/-- Transport all three objects and both arrows of a short complex through
specified isomorphisms. -/
def transportShortComplex {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) {Y₁ Y₂ Y₃ : C}
    (e₁ : S.X₁ ≅ Y₁) (e₂ : S.X₂ ≅ Y₂) (e₃ : S.X₃ ≅ Y₃) :
    ShortComplex C :=
  ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom) (by
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    simpa only [Category.assoc, zero_comp, comp_zero] using
      congrArg (fun k => e₁.inv ≫ k ≫ e₃.hom) S.zero)

/-- The original short complex is canonically isomorphic to its transported
presentation. -/
def transportShortComplexIso {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) {Y₁ Y₂ Y₃ : C}
    (e₁ : S.X₁ ≅ Y₁) (e₂ : S.X₂ ≅ Y₂) (e₃ : S.X₃ ≅ Y₃) :
    S ≅ transportShortComplex S e₁ e₂ e₃ :=
  ShortComplex.isoMk e₁ e₂ e₃ (by simp [transportShortComplex])
    (by simp [transportShortComplex])

/-- Exactness is preserved when a Mayer--Vietoris segment is rewritten on
isomorphic production homology objects. -/
theorem transportShortComplex_exact {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) {Y₁ Y₂ Y₃ : C}
    (e₁ : S.X₁ ≅ Y₁) (e₂ : S.X₂ ≅ Y₂) (e₃ : S.X₃ ≅ Y₃)
    (hS : S.Exact) :
    (transportShortComplex S e₁ e₂ e₃).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso S e₁ e₂ e₃) hS

/-- The cover-small inclusion induces an isomorphism on integral singular
homology in every degree for an open cover. -/
theorem coverSmall_homologyMap_isIso
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a)
    (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (coverSmallChains.ι U) n) := by
  cases n with
  | zero => exact coverSmall_homologyMap_isIso_zero U hUOpen hUCover
  | succ n => exact coverSmall_homologyMap_isIso_succ U hUOpen hUCover n

/-- The corresponding named comparison isomorphism from cover-small homology
to production singular homology. -/
def coverSmallHomologyIso
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a)
    (n : ℕ) :
    (coverSmallChains U).homology n ≅ (SingularChains (TopCat.of X)).homology n := by
  letI := coverSmall_homologyMap_isIso U hUOpen hUCover n
  exact asIso (HomologicalComplex.homologyMap (coverSmallChains.ι U) n)

/-- The already-compiled subcomplex Mayer--Vietoris exact segment can be
transported to any three production objects once the comparison isomorphisms
and arrow squares have been established. -/
theorem subcomplexMayerVietoris_exact_transport
    {S : SSet} (P Q : S.Subcomplex) (n : ℕ)
    {Y₁ Y₂ Y₃ : AddCommGrpCat}
    (e₁ : (subcomplexMayerVietorisShortComplex P Q).X₁.homology n ≅ Y₁)
    (e₂ : (subcomplexMayerVietorisShortComplex P Q).X₂.homology n ≅ Y₂)
    (e₃ : (subcomplexMayerVietorisShortComplex P Q).X₃.homology n ≅ Y₃) :
    (transportShortComplex
      (ShortComplex.mk
        (HomologicalComplex.homologyMap
          (subcomplexMayerVietorisShortComplex P Q).f n)
        (HomologicalComplex.homologyMap
          (subcomplexMayerVietorisShortComplex P Q).g n)
        (by
          rw [← HomologicalComplex.homologyMap_comp,
            (subcomplexMayerVietorisShortComplex P Q).zero,
            HomologicalComplex.homologyMap_zero])) e₁ e₂ e₃).Exact :=
  transportShortComplex_exact _ e₁ e₂ e₃
    (subcomplexMayerVietoris_exact_pieces P Q n)

end ConstructionTargets.ProductionOpenCoverMayerVietoris

#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex_exact
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.homologyBiprodIso_hom
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.homologyBiprodIso_inv
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.coverSmall_homologyMap_isIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.subcomplexMayerVietoris_exact_transport
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.ambientRangeProductionHomologyIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanIntersectionProductionHomologyIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanPiecesProductionHomologyIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
