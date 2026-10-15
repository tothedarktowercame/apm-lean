import Mathlib
import ConstructionTargets.CoefficientH0
import ConstructionTargets.CoefficientSubcomplexMayerVietoris
import ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence
import ConstructionTargets.CoefficientAmbientSubspaceRangeComparison
import ConstructionTargets.CoefficientIntersectionRangeComparison
import ConstructionTargets.CoefficientPieceRangeBiproductComparison
import ConstructionTargets.CoefficientHomologyBiprodIso
import ConstructionTargets.ProductionOpenCoverMayerVietoris

/-! # Integral Mayer–Vietoris for open covers (claude-14, 2026-10-15)

The `ℤ` copy of `RP3Homology.rationalMayerVietoris` (`ConstructionTargets/CP2RationalHomology.lean`):
for open `U`, `V` covering `X`, the sequence
`H_n(U ∩ V) → H_n U ⊕ H_n V → H_n X → H_{n-1}(U ∩ V)` is exact (`range = ker`), with an
existential connecting map.  The proof is coefficient-generic; only `ℚ ↦ ℤ` changed. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open ConstructionTargets

namespace IntegralMV

/-- Integral singular homology. -/
abbrev HZ (k : ℕ) (X : Type) [TopologicalSpace X] :=
  ConstructionTargets.CoefficientH0.SingularHomology ℤ k (TopCat.of X)

section MV

/-- Inclusion-induced map in rational homology. -/
def mvIncl {X : Type} [TopologicalSpace X] {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    HZ n A ⟶ HZ n B :=
  HomologicalComplex.homologyMap
    (CoefficientH0.singularPostcomposition ℤ ⟨Set.inclusion h, continuous_inclusion h⟩) n

def mvToX {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) : HZ n A ⟶ HZ n X :=
  HomologicalComplex.homologyMap
    (CoefficientH0.singularPostcomposition ℤ ⟨Subtype.val, continuous_subtype_val⟩) n

def mvI {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    HZ n ↥(U ∩ V) ⟶ HZ n U ⊞ HZ n V :=
  biprod.lift (mvIncl Set.inter_subset_left n) (mvIncl Set.inter_subset_right n)

def mvJ {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    HZ n U ⊞ HZ n V ⟶ HZ n X :=
  biprod.desc (mvToX U n) (-(mvToX V n))

lemma integralMayerVietoris_aux_smallComparison
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientSmallPath.coverSmallInclusion ℤ
        (fun b : Bool => if b then U else V)) n) := by
  apply ConstructionTargets.CoefficientSmallComparison.inclusion_isIso
  · intro b
    cases b <;> simp [hU, hV]
  · intro x _
    have hx : x ∈ U ∪ V := by rw [hcov]; trivial
    rcases hx with hx | hx
    · exact Set.mem_iUnion.2 ⟨true, by simpa using hx⟩
    · exact Set.mem_iUnion.2 ⟨false, by simpa using hx⟩

/-- Rational Mayer–Vietoris for an open cover of an arbitrary space.  LIBRARY: port
`ProductionOpenCoverMayerVietoris` (ℤ) using the coefficient pieces
`CoefficientSubcomplexMayerVietoris`, `CoefficientSubspaceUnionRangeHomologyEquivalence`,
`CoefficientAmbientSubspaceRangeComparison`, `CoefficientIntersectionRangeComparison`,
`CoefficientPieceRangeBiproductComparison`, and `ProductionOpenCoverMayerVietoris.transportShortComplex_exact`. -/
abbrev integralMayerVietoris_aux_chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)

abbrev integralMayerVietoris_aux_P {X : Type} [TopologicalSpace X] (U : Set X) :=
  ConstructionTargets.SingularExcision.ambientSubspaceRange U

noncomputable def integralMayerVietoris_aux_negIso (M : ModuleCat ℤ) : M ≅ M where
  hom := -𝟙 M
  inv := -𝟙 M
  hom_inv_id := by simp
  inv_hom_id := by simp

noncomputable def integralMayerVietoris_aux_interIso
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    ((integralMayerVietoris_aux_chains).obj
      (((integralMayerVietoris_aux_P U ⊓ integralMayerVietoris_aux_P V) :
        (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet)).homology n ≅
      HZ n ↥(U ∩ V) :=
  CoefficientIntersectionRangeComparison.infimumToIntersectionHomologyIso ℤ U V n

noncomputable def integralMayerVietoris_aux_pieceIso
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (((integralMayerVietoris_aux_chains).obj (integralMayerVietoris_aux_P U : SSet)) ⊞
      ((integralMayerVietoris_aux_chains).obj (integralMayerVietoris_aux_P V : SSet))).homology n ≅
      HZ n U ⊞ HZ n V :=
  CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n ≪≫
    CoefficientPieceRangeBiproductComparison.pieceHomologyIso ℤ U V n ≪≫
    biprod.mapIso (Iso.refl _) (integralMayerVietoris_aux_negIso _)

lemma integralMayerVietoris_aux_unionMap_isIso
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((integralMayerVietoris_aux_chains).map
        (integralMayerVietoris_aux_P U ⊔ integralMayerVietoris_aux_P V).ι) n) := by
  have h := integralMayerVietoris_aux_smallComparison U V hU hV hcov n
  have heq : ConstructionTargets.SingularSubdivision.coverSmallSSet
      (fun b : Bool => if b then U else V) =
      integralMayerVietoris_aux_P U ⊔ integralMayerVietoris_aux_P V := by
    rw [ConstructionTargets.SingularExcision.coverSmallSSet_bool_eq_sup]
    rfl
  rw [← heq]
  exact h

noncomputable def integralMayerVietoris_aux_unionIso
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) :
    ((integralMayerVietoris_aux_chains).obj
      (((integralMayerVietoris_aux_P U ⊔ integralMayerVietoris_aux_P V) :
        (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet)).homology n ≅
      HZ n X := by
  let f := HomologicalComplex.homologyMap
    ((integralMayerVietoris_aux_chains).map
      (integralMayerVietoris_aux_P U ⊔ integralMayerVietoris_aux_P V).ι) n
  exact @asIso _ _ _ _ f
    (integralMayerVietoris_aux_unionMap_isIso U V hU hV hcov n)

abbrev integralMayerVietoris_aux_SC {X : Type} [TopologicalSpace X] (U V : Set X) :=
  CoefficientSubcomplexMayerVietoris.shortComplex ℤ
    (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V)

lemma integralMayerVietoris_aux_lift_fst
    {W K L : ChainComplex (ModuleCat ℤ) ℕ} (f : W ⟶ K) (g : W ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.lift f g) n ≫
      (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ K L n).hom ≫ biprod.fst =
      HomologicalComplex.homologyMap f n := by
  rw [CoefficientHomologyBiprodIso.homologyBiprodIso_hom, biprod.lift_fst,
    ← HomologicalComplex.homologyMap_comp, biprod.lift_fst]

lemma integralMayerVietoris_aux_lift_snd
    {W K L : ChainComplex (ModuleCat ℤ) ℕ} (f : W ⟶ K) (g : W ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.lift f g) n ≫
      (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ K L n).hom ≫ biprod.snd =
      HomologicalComplex.homologyMap g n := by
  rw [CoefficientHomologyBiprodIso.homologyBiprodIso_hom, biprod.lift_snd,
    ← HomologicalComplex.homologyMap_comp, biprod.lift_snd]

lemma integralMayerVietoris_aux_interArrow_aux_fst
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (integralMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n ≫
        (integralMayerVietoris_aux_pieceIso U V n).hom ≫ biprod.fst =
      mvIncl Set.inter_subset_left n := by
  rw [show (integralMayerVietoris_aux_SC U V).f =
      biprod.lift
        ((integralMayerVietoris_aux_chains).map
          (ConstructionTargets.SingularExcision.subcomplexIntersectionToLeft
            (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V)))
        (-((integralMayerVietoris_aux_chains).map
          (ConstructionTargets.SingularExcision.subcomplexIntersectionToRight
            (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V)))) by rfl]
  have htail :
      ((ConstructionTargets.CoefficientPieceRangeBiproductComparison.pieceHomologyIso
          ℤ U V n).hom ≫
          biprod.map (𝟙 _) (integralMayerVietoris_aux_negIso _).hom) ≫ biprod.fst =
        biprod.fst ≫
          (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
            ℤ U n).hom := by
    rw [Category.assoc, biprod.map_fst]
    simp only [Category.comp_id, ← Category.assoc,
      ConstructionTargets.CoefficientPieceRangeBiproductComparison.pieceHomologyIso_hom_fst]
  have htail2 := congrArg
    (fun k => (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ
      ((integralMayerVietoris_aux_chains).obj (integralMayerVietoris_aux_P U : SSet))
      ((integralMayerVietoris_aux_chains).obj (integralMayerVietoris_aux_P V : SSet)) n).hom ≫ k)
    htail
  calc
    _ = (integralMayerVietoris_aux_interIso U V n).inv ≫
        (HomologicalComplex.homologyMap
          (biprod.lift
            ((integralMayerVietoris_aux_chains).map
              (ConstructionTargets.SingularExcision.subcomplexIntersectionToLeft
                (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V)))
            (-((integralMayerVietoris_aux_chains).map
              (ConstructionTargets.SingularExcision.subcomplexIntersectionToRight
                (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V))))) n ≫
          (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n).hom ≫
          biprod.fst) ≫
        (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
          ℤ U n).hom := by
      simp only [integralMayerVietoris_aux_pieceIso, Iso.trans_hom,
        biprod.mapIso_hom, Iso.refl_hom]
      slice_lhs 3 5 => exact htail2
      simp only [Category.assoc]
      rfl
    _ = (integralMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap
          ((integralMayerVietoris_aux_chains).map
            (ConstructionTargets.SingularExcision.subcomplexIntersectionToLeft
              (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V))) n ≫
        (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
          ℤ U n).hom := by
      rw [integralMayerVietoris_aux_lift_fst]
    _ = _ := by
      change
        (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
            ℤ (U ∩ V) n).inv ≫
          (ConstructionTargets.CoefficientIntersectionRangeComparison.intersectionHomologyIso
            ℤ U V n).hom ≫
          HomologicalComplex.homologyMap
            ((integralMayerVietoris_aux_chains).map
              (ConstructionTargets.SingularExcision.subcomplexIntersectionToLeft
                (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V))) n ≫
          (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
            ℤ U n).hom = _
      rw [ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso_hom]
      have hs :=
        ConstructionTargets.CoefficientIntersectionRangeNaturality.homology_square_left
          ℤ U V n
      slice_lhs 3 4 =>
        exact hs.symm
      rw [HomologicalComplex.homologyMap_comp]
      change
        (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
            ℤ (U ∩ V) n).inv ≫
          (ConstructionTargets.CoefficientIntersectionRangeComparison.intersectionHomologyIso
            ℤ U V n).hom ≫
          ((ConstructionTargets.CoefficientIntersectionRangeComparison.intersectionHomologyIso
            ℤ U V n).inv ≫
            (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
              ℤ (U ∩ V) n).hom) ≫
          HomologicalComplex.homologyMap
            ((integralMayerVietoris_aux_chains).map
              (TopCat.toSSet.map
                (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion
                  Set.inter_subset_left))) n = _
      simp [mvIncl, Category.assoc]
      rfl

lemma integralMayerVietoris_aux_interArrow_aux_snd
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (integralMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n ≫
        (integralMayerVietoris_aux_pieceIso U V n).hom ≫ biprod.snd =
      mvIncl Set.inter_subset_right n := by
  have hpiece : (integralMayerVietoris_aux_pieceIso U V n).hom ≫ biprod.snd =
      (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n).hom ≫
        biprod.snd ≫ (CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso ℤ V n).hom ≫
        (integralMayerVietoris_aux_negIso _).hom := by
    simp only [integralMayerVietoris_aux_pieceIso, Iso.trans_hom,
      biprod.mapIso_hom, Category.assoc, biprod.map_snd]
    simpa only [Category.assoc] using congrArg
      (fun k => (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n).hom ≫
        k ≫ (integralMayerVietoris_aux_negIso _).hom)
      (CoefficientPieceRangeBiproductComparison.pieceHomologyIso_hom_snd ℤ U V n)
  calc
    _ = ((integralMayerVietoris_aux_interIso U V n).inv ≫
          HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n) ≫
        ((integralMayerVietoris_aux_pieceIso U V n).hom ≫ biprod.snd) := by
          simp only [Category.assoc]
    _ = ((integralMayerVietoris_aux_interIso U V n).inv ≫
          HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n) ≫
        ((CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n).hom ≫
          biprod.snd ≫
          (CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso ℤ V n).hom ≫
          (integralMayerVietoris_aux_negIso _).hom) := by
            exact congrArg (fun k =>
              ((integralMayerVietoris_aux_interIso U V n).inv ≫
                HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n) ≫ k)
              hpiece
    _ = _ := by
      have hcomponent :
          HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n ≫
              (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n).hom ≫ biprod.snd =
            -HomologicalComplex.homologyMap
              ((integralMayerVietoris_aux_chains).map
                (ConstructionTargets.SingularExcision.subcomplexIntersectionToRight
                  (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V))) n := by
        change HomologicalComplex.homologyMap
            (biprod.lift
              ((integralMayerVietoris_aux_chains).map
                (ConstructionTargets.SingularExcision.subcomplexIntersectionToLeft
                  (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V)))
              (-((integralMayerVietoris_aux_chains).map
                (ConstructionTargets.SingularExcision.subcomplexIntersectionToRight
                  (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V))))) n ≫
              (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n).hom ≫ biprod.snd = _
        rw [integralMayerVietoris_aux_lift_snd]
        rw [HomologicalComplex.homologyMap_neg]
      rw [show (integralMayerVietoris_aux_negIso _).hom = -𝟙 _ by rfl]
      simp only [Category.assoc]
      have hc := congrArg (fun k =>
        (integralMayerVietoris_aux_interIso U V n).inv ≫ k ≫
          (CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso ℤ V n).hom ≫
          (-𝟙 _)) hcomponent
      have hc' :
          (integralMayerVietoris_aux_interIso U V n).inv ≫
              HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n ≫
              (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n).hom ≫ biprod.snd ≫
              (CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso ℤ V n).hom ≫ (-𝟙 _) =
            (integralMayerVietoris_aux_interIso U V n).inv ≫
              (-HomologicalComplex.homologyMap
                ((integralMayerVietoris_aux_chains).map
                  (ConstructionTargets.SingularExcision.subcomplexIntersectionToRight
                    (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V))) n) ≫
              (CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso ℤ V n).hom ≫ (-𝟙 _) := by
        simpa only [Category.assoc] using hc
      rw [hc']
      simp only [Preadditive.comp_neg, Preadditive.neg_comp, neg_neg, Category.comp_id]
      have hsquare :=
        ConstructionTargets.CoefficientIntersectionRangeNaturality.homology_square_right
          ℤ U V n
      have hsquare' : (integralMayerVietoris_aux_interIso U V n).hom ≫
            mvIncl Set.inter_subset_right n =
          HomologicalComplex.homologyMap
              ((integralMayerVietoris_aux_chains).map
                (ConstructionTargets.SingularExcision.subcomplexIntersectionToRight
                  (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V))) n ≫
            (CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso ℤ V n).hom := by
        simpa [integralMayerVietoris_aux_interIso,
          CoefficientIntersectionRangeComparison.infimumToIntersectionHomologyIso_hom,
          CoefficientIntersectionRangeComparison.intersectionHomologyIso,
          CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso_hom,
          HomologicalComplex.homologyMap_comp, mvIncl,
          CoefficientH0.singularPostcomposition] using hsquare
      rw [← hsquare']
      simp

lemma integralMayerVietoris_aux_interArrow
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (integralMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n ≫
        (integralMayerVietoris_aux_pieceIso U V n).hom = mvI U V n := by
  apply biprod.hom_ext
  · simpa [mvI] using integralMayerVietoris_aux_interArrow_aux_fst U V n
  · simpa [mvI] using integralMayerVietoris_aux_interArrow_aux_snd U V n
lemma integralMayerVietoris_aux_unionArrow_aux_inl
    {K L T : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ T) (g : L ⟶ T) (n : ℕ) :
    biprod.inl ≫ (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ K L n).inv ≫
        HomologicalComplex.homologyMap (biprod.desc f g) n =
      HomologicalComplex.homologyMap f n := by
  rw [CoefficientHomologyBiprodIso.homologyBiprodIso_inv,
    biprod.inl_desc_assoc, ← HomologicalComplex.homologyMap_comp, biprod.inl_desc]

lemma integralMayerVietoris_aux_unionArrow_aux_inr
    {K L T : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ T) (g : L ⟶ T) (n : ℕ) :
    biprod.inr ≫ (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ K L n).inv ≫
        HomologicalComplex.homologyMap (biprod.desc f g) n =
      HomologicalComplex.homologyMap g n := by
  rw [CoefficientHomologyBiprodIso.homologyBiprodIso_inv,
    biprod.inr_desc_assoc, ← HomologicalComplex.homologyMap_comp, biprod.inr_desc]

lemma integralMayerVietoris_aux_unionArrow_aux_component
    {X : Type} [TopologicalSpace X] (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
        ℤ A n).inv ≫
      HomologicalComplex.homologyMap
        ((integralMayerVietoris_aux_chains).map
          (ConstructionTargets.SingularExcision.ambientSubspaceRangeInclusion h)) n ≫
      (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
        ℤ B n).hom =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℤ
          ⟨Set.inclusion h, continuous_inclusion h⟩) n := by
  calc
    _ = (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
          ℤ A n).inv ≫
        (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
          ℤ A n).hom ≫
        HomologicalComplex.homologyMap
          ((integralMayerVietoris_aux_chains).map
            (TopCat.toSSet.map
              (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion h))) n := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦
          (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
            ℤ A n).inv ≫ k)
        (ConstructionTargets.CoefficientAmbientSubspaceRangeNaturality.homology_square
          ℤ h n).symm
    _ = _ := by simp; rfl

lemma integralMayerVietoris_aux_unionArrow_aux_ambient
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
        ℤ A n).inv ≫
      HomologicalComplex.homologyMap
        ((integralMayerVietoris_aux_chains).map
          (integralMayerVietoris_aux_P A).ι) n =
      mvToX A n := by
  rw [ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso_inv,
    ← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun f ↦ HomologicalComplex.homologyMap f n)
  apply (cancel_epi
    (ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeChainsIso
      ℤ A).hom).1
  simpa [mvToX, CoefficientRelativeSmall.subspaceMap, Category.assoc] using
    (ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility.ambientSubspaceRangeChainsIso_hom_comp_subspaceMap
      ℤ A).symm

lemma integralMayerVietoris_aux_unionArrow
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) :
    (integralMayerVietoris_aux_pieceIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).g n ≫
        (integralMayerVietoris_aux_unionIso U V hU hV hcov n).hom = mvJ U V n := by
  apply biprod.hom_ext'
  · simp only [integralMayerVietoris_aux_pieceIso, Iso.trans_inv, Category.assoc]
    change biprod.inl ≫
      (biprod.map (𝟙 _) (-𝟙 _) ≫
        (CoefficientPieceRangeBiproductComparison.pieceHomologyIso ℤ U V n).inv ≫
        (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n).inv) ≫
      HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).g n ≫
      (integralMayerVietoris_aux_unionIso U V hU hV hcov n).hom = _
    simp only [Category.assoc]
    rw [biprod.inl_map_assoc]
    simp only [Category.id_comp]
    dsimp [CoefficientPieceRangeBiproductComparison.pieceHomologyIso]
    rw [biprod.inl_map_assoc]
    dsimp [integralMayerVietoris_aux_SC,
      CoefficientSubcomplexMayerVietoris.shortComplex]
    slice_lhs 2 4 =>
      rw [integralMayerVietoris_aux_unionArrow_aux_inl]
    change _ ≫ HomologicalComplex.homologyMap
      ((integralMayerVietoris_aux_chains).map
        (ConstructionTargets.SingularExcision.subcomplexLeftToUnion
          (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V))) n ≫
      HomologicalComplex.homologyMap
        ((integralMayerVietoris_aux_chains).map
          (integralMayerVietoris_aux_P U ⊔ integralMayerVietoris_aux_P V).ι) n = _
    slice_lhs 2 3 => rw [← HomologicalComplex.homologyMap_comp]
    rw [← Functor.map_comp]
    change _ ≫ HomologicalComplex.homologyMap
      ((integralMayerVietoris_aux_chains).map (integralMayerVietoris_aux_P U).ι) n = _
    simpa [mvJ] using integralMayerVietoris_aux_unionArrow_aux_ambient U n
  · simp only [integralMayerVietoris_aux_pieceIso, Iso.trans_inv, Category.assoc]
    change biprod.inr ≫
      (biprod.map (𝟙 _) (-𝟙 _) ≫
        (CoefficientPieceRangeBiproductComparison.pieceHomologyIso ℤ U V n).inv ≫
        (CoefficientHomologyBiprodIso.homologyBiprodIso ℤ _ _ n).inv) ≫
      HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).g n ≫
      (integralMayerVietoris_aux_unionIso U V hU hV hcov n).hom = _
    simp only [Category.assoc]
    rw [biprod.inr_map_assoc]
    dsimp [CoefficientPieceRangeBiproductComparison.pieceHomologyIso]
    rw [Preadditive.neg_comp, biprod.inr_map_assoc]
    dsimp [integralMayerVietoris_aux_SC,
      CoefficientSubcomplexMayerVietoris.shortComplex]
    simp only [Category.id_comp]
    slice_lhs 3 5 => rw [integralMayerVietoris_aux_unionArrow_aux_inr]
    change -((ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
      ℤ V n).inv ≫ HomologicalComplex.homologyMap
        ((integralMayerVietoris_aux_chains).map
          (ConstructionTargets.SingularExcision.subcomplexRightToUnion
            (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V))) n ≫
        HomologicalComplex.homologyMap
          ((integralMayerVietoris_aux_chains).map
            (integralMayerVietoris_aux_P U ⊔ integralMayerVietoris_aux_P V).ι) n) = _
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    change -((ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso
      ℤ V n).inv ≫ HomologicalComplex.homologyMap
        ((integralMayerVietoris_aux_chains).map (integralMayerVietoris_aux_P V).ι) n) = _
    rw [integralMayerVietoris_aux_unionArrow_aux_ambient]
    simp [mvJ]
    rfl

/-- Transport of the subcomplex Mayer–Vietoris sequence (`CoefficientSubcomplexMayerVietoris`:
exactness at pieces/union/intersection + connecting map) along `interIso`, `pieceIso`,
`unionIso`, given that the transported arrows are `mvI` and `mvJ`. -/
lemma integralMayerVietoris_aux_transport_aux_pieces
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hI : ∀ n, (integralMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n ≫
        (integralMayerVietoris_aux_pieceIso U V n).hom = mvI U V n)
    (hJ : ∀ n, (integralMayerVietoris_aux_pieceIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).g n ≫
        (integralMayerVietoris_aux_unionIso U V hU hV hcov n).hom = mvJ U V n)
    (n : ℕ) :
    LinearMap.range (mvI U V n).hom = LinearMap.ker (mvJ U V n).hom := by
  have hex := ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex_exact
    _
    (integralMayerVietoris_aux_interIso U V n)
    (integralMayerVietoris_aux_pieceIso U V n)
    (integralMayerVietoris_aux_unionIso U V hU hV hcov n)
    (CoefficientSubcomplexMayerVietoris.exact_pieces ℤ
      (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V) n)
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  dsimp only [ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex] at hex
  have hI' := hI n
  have hJ' := hJ n
  dsimp only [integralMayerVietoris_aux_SC] at hI' hJ'
  have hIhom := congrArg ModuleCat.Hom.hom hI'
  have hJhom := congrArg ModuleCat.Hom.hom hJ'
  have hIrange : LinearMap.range (mvI U V n).hom =
      LinearMap.range ((integralMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap
          (CoefficientSubcomplexMayerVietoris.shortComplex ℤ
            (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V)).f n ≫
        (integralMayerVietoris_aux_pieceIso U V n).hom).hom := by
    exact hIhom ▸ rfl
  have hJker : LinearMap.ker
      ((integralMayerVietoris_aux_pieceIso U V n).inv ≫
        HomologicalComplex.homologyMap
          (CoefficientSubcomplexMayerVietoris.shortComplex ℤ
            (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V)).g n ≫
        (integralMayerVietoris_aux_unionIso U V hU hV hcov n).hom).hom =
      LinearMap.ker (mvJ U V n).hom := by
    exact hJhom ▸ rfl
  exact hIrange.trans (hex.trans hJker)

lemma integralMayerVietoris_aux_transport_aux_union
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hJ : ∀ n, (integralMayerVietoris_aux_pieceIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).g n ≫
        (integralMayerVietoris_aux_unionIso U V hU hV hcov n).hom = mvJ U V n)
    (n : ℕ) :
    LinearMap.range (mvJ U V (n + 1)).hom = LinearMap.ker
      ((integralMayerVietoris_aux_unionIso U V hU hV hcov (n + 1)).inv ≫
        CoefficientSubcomplexMayerVietoris.connecting ℤ
          (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V) n ≫
        (integralMayerVietoris_aux_interIso U V n).hom).hom := by
  have hex := ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex_exact
    _
    (integralMayerVietoris_aux_pieceIso U V (n + 1))
    (integralMayerVietoris_aux_unionIso U V hU hV hcov (n + 1))
    (integralMayerVietoris_aux_interIso U V n)
    (CoefficientSubcomplexMayerVietoris.exact_union ℤ
      (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V) n)
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  dsimp only [ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex] at hex
  have hJ' := hJ (n + 1)
  dsimp only [integralMayerVietoris_aux_SC] at hJ'
  have hJhom := congrArg ModuleCat.Hom.hom hJ'
  have hJrange : LinearMap.range (mvJ U V (n + 1)).hom = LinearMap.range
      ((integralMayerVietoris_aux_pieceIso U V (n + 1)).inv ≫
        HomologicalComplex.homologyMap
          (CoefficientSubcomplexMayerVietoris.shortComplex ℤ
            (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V)).g (n + 1) ≫
        (integralMayerVietoris_aux_unionIso U V hU hV hcov (n + 1)).hom).hom := by
    exact hJhom ▸ rfl
  exact hJrange.trans hex

lemma integralMayerVietoris_aux_transport_aux_intersection
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hI : ∀ n, (integralMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n ≫
        (integralMayerVietoris_aux_pieceIso U V n).hom = mvI U V n)
    (n : ℕ) :
    LinearMap.range
      ((integralMayerVietoris_aux_unionIso U V hU hV hcov (n + 1)).inv ≫
        CoefficientSubcomplexMayerVietoris.connecting ℤ
          (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V) n ≫
        (integralMayerVietoris_aux_interIso U V n).hom).hom =
      LinearMap.ker (mvI U V n).hom := by
  have hex := ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex_exact
    _
    (integralMayerVietoris_aux_unionIso U V hU hV hcov (n + 1))
    (integralMayerVietoris_aux_interIso U V n)
    (integralMayerVietoris_aux_pieceIso U V n)
    (CoefficientSubcomplexMayerVietoris.exact_intersection ℤ
      (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V) n)
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  dsimp only [ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex] at hex
  have hI' := hI n
  dsimp only [integralMayerVietoris_aux_SC] at hI'
  have hIhom := congrArg ModuleCat.Hom.hom hI'
  have hIker : LinearMap.ker
      ((integralMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap
          (CoefficientSubcomplexMayerVietoris.shortComplex ℤ
            (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V)).f n ≫
        (integralMayerVietoris_aux_pieceIso U V n).hom).hom =
      LinearMap.ker (mvI U V n).hom := by
    exact hIhom ▸ rfl
  exact hex.trans hIker

lemma integralMayerVietoris_aux_transport
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hI : ∀ n, (integralMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).f n ≫
        (integralMayerVietoris_aux_pieceIso U V n).hom = mvI U V n)
    (hJ : ∀ n, (integralMayerVietoris_aux_pieceIso U V n).inv ≫
        HomologicalComplex.homologyMap (integralMayerVietoris_aux_SC U V).g n ≫
        (integralMayerVietoris_aux_unionIso U V hU hV hcov n).hom = mvJ U V n) :
    ∃ δ : ∀ n, HZ (n + 1) X ⟶ HZ n ↥(U ∩ V),
      (∀ n, LinearMap.range (mvI U V n).hom = LinearMap.ker (mvJ U V n).hom) ∧
      (∀ n, LinearMap.range (mvJ U V (n + 1)).hom = LinearMap.ker (δ n).hom) ∧
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (mvI U V n).hom) := by
  let δ : ∀ n, HZ (n + 1) X ⟶ HZ n ↥(U ∩ V) := fun n =>
    (integralMayerVietoris_aux_unionIso U V hU hV hcov (n + 1)).inv ≫
      CoefficientSubcomplexMayerVietoris.connecting ℤ
        (integralMayerVietoris_aux_P U) (integralMayerVietoris_aux_P V) n ≫
      (integralMayerVietoris_aux_interIso U V n).hom
  refine ⟨δ, fun n => integralMayerVietoris_aux_transport_aux_pieces
    U V hU hV hcov hI hJ n, ?_, ?_⟩
  · intro n
    exact integralMayerVietoris_aux_transport_aux_union U V hU hV hcov hJ n
  · intro n
    exact integralMayerVietoris_aux_transport_aux_intersection U V hU hV hcov hI n

theorem integralMayerVietoris {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∃ δ : ∀ n, HZ (n + 1) X ⟶ HZ n ↥(U ∩ V),
      (∀ n, LinearMap.range (mvI U V n).hom = LinearMap.ker (mvJ U V n).hom) ∧
      (∀ n, LinearMap.range (mvJ U V (n + 1)).hom = LinearMap.ker (δ n).hom) ∧
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (mvI U V n).hom) :=
  integralMayerVietoris_aux_transport U V hU hV hcov
    (fun n => integralMayerVietoris_aux_interArrow U V n)
    (fun n => integralMayerVietoris_aux_unionArrow U V hU hV hcov n)

end MV

end IntegralMV
