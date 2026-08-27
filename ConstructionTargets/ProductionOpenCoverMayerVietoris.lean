import ConstructionTargets.BooleanTwoCoverScaffold
import ConstructionTargets.HomologyBiprodIso
import ConstructionTargets.HomologyBiprodNormalization

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
open ConstructionTargets.HomologyBiprodIso

private abbrev ssetChains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

/-- Homology of an ambient range subcomplex as the production singular
homology of its underlying topological subspace. -/
noncomputable def ambientRangeProductionHomologyIso
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ssetChains.obj (ambientSubspaceRange A : SSet)).homology n ≅
      (SingularChains (TopCat.of A)).homology n :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) n).mapIso (ambientSubspaceRangeChainsIso A)

theorem ambientRangeProductionHomologyIso_hom
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ambientRangeProductionHomologyIso A n).hom =
      HomologicalComplex.homologyMap
        (ambientSubspaceRangeChainsIso A).hom n := by
  rfl

theorem ambientRangeProductionHomologyIso_inv
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ambientRangeProductionHomologyIso A n).inv =
      HomologicalComplex.homologyMap
        (ambientSubspaceRangeChainsIso A).inv n := by
  rfl

/-- The stored Boolean-cover intersection term as production homology of
`U ∩ V`. -/
noncomputable def booleanIntersectionProductionHomologyIso
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    ((shortComplex U V).X₁).homology n ≅
      (SingularChains (TopCat.of (U ∩ V : Set X))).homology n :=
  (ambientIntersectionRangeHomologyIso U V n).symm ≪≫
    ambientRangeProductionHomologyIso (U ∩ V) n

theorem booleanIntersectionProductionHomologyIso_hom
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (booleanIntersectionProductionHomologyIso U V n).hom =
      (ambientIntersectionRangeHomologyIso U V n).inv ≫
        (ambientRangeProductionHomologyIso (U ∩ V) n).hom := by
  rfl

theorem booleanIntersectionProductionHomologyIso_inv
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (booleanIntersectionProductionHomologyIso U V n).inv =
      (ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
        (ambientIntersectionRangeHomologyIso U V n).hom := by
  rfl

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

theorem booleanPiecesProductionHomologyIso_hom
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (booleanPiecesProductionHomologyIso U V n).hom =
      (homologyBiprodIso
        (ssetChains.obj (leftRange U : SSet))
        (ssetChains.obj (rightRange V : SSet)) n).hom ≫
      biprod.map
        (ambientRangeProductionHomologyIso U n).hom
        (ambientRangeProductionHomologyIso V n).hom := by
  rfl

theorem booleanPiecesProductionHomologyIso_inv
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (booleanPiecesProductionHomologyIso U V n).inv =
      biprod.map
        (ambientRangeProductionHomologyIso U n).inv
        (ambientRangeProductionHomologyIso V n).inv ≫
      (homologyBiprodIso
        (ssetChains.obj (leftRange U : SSet))
        (ssetChains.obj (rightRange V : SSet)) n).inv := by
  rfl

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

/-- The stored Boolean-cover intersection map becomes the actual signed pair
of subspace inclusions under the production homology identifications. -/
theorem booleanIntersectionArrow_eq_production
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (booleanIntersectionProductionHomologyIso U V n).inv ≫
        HomologicalComplex.homologyMap (shortComplex U V).f n ≫
        (booleanPiecesProductionHomologyIso U V n).hom =
      productionIntersectionArrow U V n := by
  rw [show (shortComplex U V).f =
      biprod.lift
        (ssetChains.map (subcomplexIntersectionToLeft
          (leftRange U) (rightRange V)))
        (-ssetChains.map (subcomplexIntersectionToRight
          (leftRange U) (rightRange V))) by rfl]
  apply biprod.hom_ext
  · simp only [booleanIntersectionProductionHomologyIso_inv,
      booleanPiecesProductionHomologyIso_hom, productionIntersectionArrow,
      biprod.lift_fst]
    calc
      _ = (((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
              (ambientIntersectionRangeHomologyIso U V n).hom) ≫
            HomologicalComplex.homologyMap
              (ssetChains.map (subcomplexIntersectionToLeft
                (leftRange U) (rightRange V))) n) ≫
          (ambientRangeProductionHomologyIso U n).hom := by
            exact ConstructionTargets.HomologyBiprodNormalization.fullyLeftAssociated_homologyMap_signedLift_biprodIso_map_fst
                n _ _ _ _ _
      _ = _ := by
        calc
          _ = ((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
                HomologicalComplex.homologyMap
                  (ssetChains.map (ambientSubspaceRangeInclusion
                    Set.inter_subset_left)) n) ≫
              (ambientRangeProductionHomologyIso U n).hom := by
                simpa only [Category.assoc, leftRange, rightRange] using
                  congrArg (fun k ↦
                    ((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫ k) ≫
                      (ambientRangeProductionHomologyIso U n).hom)
                    (ambientIntersectionRangeHomologyIso_hom_comp_left U V n)
          _ = ((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
                (ambientRangeProductionHomologyIso (U ∩ V) n).hom) ≫
              HomologicalComplex.homologyMap
                (ssetChains.map (TopCat.toSSet.map
                  (topologicalSubspaceInclusion Set.inter_subset_left))) n := by
                simpa only [ambientRangeProductionHomologyIso_hom,
                  Category.assoc] using
                  congrArg (fun k ↦
                    (ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫ k)
                    (ambientSubspaceRangeHomologyIso_naturality
                      Set.inter_subset_left n).symm
          _ = _ := by simp
  · simp only [booleanIntersectionProductionHomologyIso_inv,
      booleanPiecesProductionHomologyIso_hom, productionIntersectionArrow,
      biprod.lift_snd]
    calc
      _ = (((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
              (ambientIntersectionRangeHomologyIso U V n).hom) ≫
            (-HomologicalComplex.homologyMap
              (ssetChains.map (subcomplexIntersectionToRight
                (leftRange U) (rightRange V))) n)) ≫
          (ambientRangeProductionHomologyIso V n).hom := by
            exact ConstructionTargets.HomologyBiprodNormalization.fullyLeftAssociated_homologyMap_signedLift_biprodIso_map_snd
                n _ _ _ _ _
      _ = _ := by
        have hp :
            (((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
                (ambientIntersectionRangeHomologyIso U V n).hom) ≫
              HomologicalComplex.homologyMap
                (ssetChains.map (subcomplexIntersectionToRight
                  (leftRange U) (rightRange V))) n) ≫
              (ambientRangeProductionHomologyIso V n).hom =
            HomologicalComplex.homologyMap
              (ssetChains.map (TopCat.toSSet.map
                (topologicalSubspaceInclusion Set.inter_subset_right))) n := by
          calc
          _ = ((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
                HomologicalComplex.homologyMap
                  (ssetChains.map (ambientSubspaceRangeInclusion
                    Set.inter_subset_right)) n) ≫
              (ambientRangeProductionHomologyIso V n).hom := by
                simpa only [Category.assoc, leftRange, rightRange] using
                  congrArg (fun k ↦
                    ((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫ k) ≫
                      (ambientRangeProductionHomologyIso V n).hom)
                    (ambientIntersectionRangeHomologyIso_hom_comp_right U V n)
          _ = ((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
                (ambientRangeProductionHomologyIso (U ∩ V) n).hom) ≫
              HomologicalComplex.homologyMap
                (ssetChains.map (TopCat.toSSet.map
                  (topologicalSubspaceInclusion Set.inter_subset_right))) n := by
                simpa only [ambientRangeProductionHomologyIso_hom,
                  Category.assoc] using
                  congrArg (fun k ↦
                    (ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫ k)
                    (ambientSubspaceRangeHomologyIso_naturality
                      Set.inter_subset_right n).symm
          _ = _ := by simp
        calc
          _ = (-(
              ((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
                (ambientIntersectionRangeHomologyIso U V n).hom) ≫
              HomologicalComplex.homologyMap
                (ssetChains.map (subcomplexIntersectionToRight
                  (leftRange U) (rightRange V))) n)) ≫
              (ambientRangeProductionHomologyIso V n).hom := by
                exact congrArg
                  (fun k ↦ k ≫ (ambientRangeProductionHomologyIso V n).hom)
                  (Preadditive.comp_neg _ _)
          _ = -((((ambientRangeProductionHomologyIso (U ∩ V) n).inv ≫
                (ambientIntersectionRangeHomologyIso U V n).hom) ≫
              HomologicalComplex.homologyMap
                (ssetChains.map (subcomplexIntersectionToRight
                  (leftRange U) (rightRange V))) n) ≫
              (ambientRangeProductionHomologyIso V n).hom) := by
                exact Preadditive.neg_comp _ _
          _ = _ := congrArg Neg.neg hp

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

/-- Equality-induced identification of the stored Boolean union with the
generic cover-small simplicial object. -/
noncomputable def booleanSmallSSetIso
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    (smallSSet U V : SSet) ≅
      (coverSmallSSet (booleanCover U V) : SSet) :=
  smallSSetIsoCoverSmall U V

/-- Chain-level form of `booleanSmallSSetIso`. -/
noncomputable def booleanSmallChainsIso
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    ssetChains.obj (smallSSet U V : SSet) ≅
      coverSmallChains (booleanCover U V) :=
  ssetChains.mapIso (booleanSmallSSetIso U V)

/-- Homology-level form of the stored/generic Boolean-cover identification. -/
noncomputable def booleanSmallHomologyIso
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (ssetChains.obj (smallSSet U V : SSet)).homology n ≅
      (coverSmallChains (booleanCover U V)).homology n :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) n).mapIso (booleanSmallChainsIso U V)

theorem booleanSmallHomologyIso_hom
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (booleanSmallHomologyIso U V n).hom =
      HomologicalComplex.homologyMap (booleanSmallChainsIso U V).hom n := by
  rfl

theorem booleanSmallHomologyIso_inv
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (booleanSmallHomologyIso U V n).inv =
      HomologicalComplex.homologyMap (booleanSmallChainsIso U V).inv n := by
  rfl

theorem booleanSmallChainsIso_hom_comp_ambient
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    (booleanSmallChainsIso U V).hom ≫
        coverSmallChains.ι (booleanCover U V) =
      ssetChains.map (smallSSet U V).ι := by
  change ssetChains.map _ ≫ ssetChains.map _ = ssetChains.map _
  rw [← Functor.map_comp]
  change ssetChains.map ((smallSSetIsoCoverSmall U V).hom ≫
    (coverSmallSSet (booleanCover U V)).ι) = _
  rw [smallSSetIsoCoverSmall_hom_comp_ambient]

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
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.coverSmall_homologyMap_isIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.subcomplexMayerVietoris_exact_transport
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.ambientRangeProductionHomologyIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanIntersectionProductionHomologyIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanPiecesProductionHomologyIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.ambientRangeProductionHomologyIso_hom
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanIntersectionProductionHomologyIso_hom
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanPiecesProductionHomologyIso_hom
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanIntersectionArrow_eq_production
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanSmallSSetIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanSmallChainsIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanSmallHomologyIso
#print axioms ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanSmallChainsIso_hom_comp_ambient
