import ConstructionTargets.CoefficientPushoutRelative
noncomputable section
namespace ConstructionTargets.CoefficientExcision
open CategoryTheory CategoryTheory.Limits
open SingularExcision SingularHomologyConcrete
variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] (A Z : Set X)
abbrev chains := CoefficientRelativeSmall.chains R
abbrev excisionComplementSC
    {X : Type} [TopologicalSpace X] (Z : Set X) :=
  ambientSubspaceRange (Zᶜ : Set X)

abbrev excisionIntersectionSC
    {X : Type} [TopologicalSpace X] (A Z : Set X) :=
  ambientSubspaceRange A ⊓ excisionComplementSC Z

abbrev excisionRestrictedSC
    {X : Type} [TopologicalSpace X] (A Z : Set X) :=
  excisionIntersectionSC A Z ⊔ ambientSubspaceRange (interior A)

abbrev excisionAmbientSC
    {X : Type} [TopologicalSpace X] (A Z : Set X) :=
  excisionComplementSC Z ⊔ ambientSubspaceRange (interior A)

def excisionRestrictedToAmbient
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionRestrictedSC A Z : SSet) ⟶
      (excisionAmbientSC A Z : SSet) :=
  SSet.Subcomplex.homOfLE (excisionSubcomplex_bicartSq A Z).le₃₄


def excisionIntersectionToComplement
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionIntersectionSC A Z : SSet) ⟶
      (excisionComplementSC Z : SSet) :=
  SSet.Subcomplex.homOfLE (excisionSubcomplex_bicartSq A Z).le₁₂

def excisionComplementToAmbient
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionComplementSC Z : SSet) ⟶ (excisionAmbientSC A Z : SSet) :=
  SSet.Subcomplex.homOfLE (excisionSubcomplex_bicartSq A Z).le₂₄

noncomputable def excisionNamedIsPushout
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    IsPushout
      (SSet.Subcomplex.homOfLE (excisionSubcomplex_bicartSq A Z).le₁₃)
      (excisionIntersectionToComplement A Z)
      (excisionRestrictedToAmbient A Z)
      (excisionComplementToAmbient A Z) := by
  exact (excisionSubcomplex_isPushout A Z).flip


def excisionIntersectionRangeSSetIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionIntersectionSC A Z : SSet) ≅
      TopCat.toSSet.obj (TopCat.of (excisedSubspace A Z)) :=
  eqToIso (congrArg
      (fun P : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex ↦ (P : SSet))
      (ambientSubspaceRange_inf A Zᶜ)) ≪≫
    (asIso (Subfunctor.toRange (TopCat.toSSet.map
      (subspaceInclusion (A ∩ Zᶜ : Set X))))).symm ≪≫
    TopCat.toSSet.mapIso (excisionIntersectionTopCatIso A Z).symm

def excisionComplementRangeSSetIso
    {X : Type} [TopologicalSpace X] (Z : Set X) :
    (excisionComplementSC Z : SSet) ≅
      TopCat.toSSet.obj (TopCat.of (Zᶜ : Set X)) :=
  (asIso (Subfunctor.toRange
    (TopCat.toSSet.map (subspaceInclusion (Zᶜ : Set X))))).symm


noncomputable def excisionComplementRangeChainsIso
    {X : Type} [TopologicalSpace X] (Z : Set X) :
    (chains R).obj (excisionComplementSC Z : SSet) ≅
      CoefficientH0.SingularChains R (TopCat.of (Zᶜ : Set X)) :=
  (chains R).mapIso (excisionComplementRangeSSetIso Z)

noncomputable def excisionIntersectionRangeChainsIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (chains R).obj (excisionIntersectionSC A Z : SSet) ≅
      CoefficientH0.SingularChains R (TopCat.of (excisedSubspace A Z)) :=
  (chains R).mapIso (excisionIntersectionRangeSSetIso A Z)


theorem excisionSourceChain_square
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (chains R).map (excisionIntersectionToComplement A Z) ≫
        (excisionComplementRangeChainsIso R Z).hom =
      (excisionIntersectionRangeChainsIso R A Z).hom ≫
        CoefficientRelativeSmall.subspaceMap R (excisedSubspace A Z) := by
  change (chains R).map _ ≫ (chains R).map _ =
    (chains R).map _ ≫ (chains R).map _
  rw [← (chains R).map_comp, ← (chains R).map_comp]
  congr 1
  exact excisionSourceSSet_square A Z

/-- The source cokernel in the simplicial excision square is the production
relative cokernel of the excised pair. -/
noncomputable def excisionSourceRelativeIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    cokernel ((chains R).map (excisionIntersectionToComplement A Z)) ≅
      cokernel (CoefficientRelativeSmall.subspaceMap R (excisedSubspace A Z)) :=
  cokernel.mapIso
    (f := (chains R).map (excisionIntersectionToComplement A Z))
    (CoefficientRelativeSmall.subspaceMap R (excisedSubspace A Z))
    (excisionIntersectionRangeChainsIso R A Z)
    (excisionComplementRangeChainsIso R Z)
    (excisionSourceChain_square R A Z)


noncomputable def excisionAmbientSmallChainsIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (chains R).obj (excisionAmbientSC A Z : SSet) ≅
      CoefficientSmallPath.coverSmallChains R (excisionCover A Z) :=
  (chains R).mapIso (excisionAmbientSmallSSetIso A Z)

noncomputable def excisionRestrictedSmallChainsIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (chains R).obj (excisionRestrictedSC A Z : SSet) ≅
      CoefficientSmallPath.coverSmallChains R
        (restrictedCover A (excisionCover A Z)) :=
  (chains R).mapIso (excisionRestrictedSmallSSetIso A Z)


theorem excisionTargetChain_square
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (chains R).map (excisionRestrictedToAmbient A Z) ≫
        (excisionAmbientSmallChainsIso R A Z).hom =
      (excisionRestrictedSmallChainsIso R A Z).hom ≫
        CoefficientRelativeSmall.restrictedMap R A (excisionCover A Z) := by
  change (chains R).map _ ≫ (chains R).map _ =
    (chains R).map _ ≫ (chains R).map _
  rw [← (chains R).map_comp, ← (chains R).map_comp]
  congr 1
  exact excisionTargetSSet_square A Z

/-- The target cokernel in the simplicial excision square is canonically the
cover-small relative cokernel used by the homology comparison. -/
noncomputable def excisionTargetSmallRelativeIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    cokernel ((chains R).map (excisionRestrictedToAmbient A Z)) ≅
      cokernel (CoefficientRelativeSmall.restrictedMap R A (excisionCover A Z)) :=
  cokernel.mapIso
    (f := (chains R).map (excisionRestrictedToAmbient A Z))
    (CoefficientRelativeSmall.restrictedMap R A (excisionCover A Z))
    (excisionRestrictedSmallChainsIso R A Z)
    (excisionAmbientSmallChainsIso R A Z)
    (excisionTargetChain_square R A Z)


def smallIso := (excisionSourceRelativeIso R A Z).symm ≪≫
  CoefficientPushoutRelative.relativeIso R (excisionNamedIsPushout A Z) ≪≫
  excisionTargetSmallRelativeIso R A Z


def pairInclusion : TopCat.of (excisedSubspace A Z) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun x => ⟨x.1.1, x.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

theorem pair_square : subspaceInclusion (excisedSubspace A Z) ≫ subspaceInclusion (Zᶜ : Set X) =
    pairInclusion A Z ≫ subspaceInclusion A := by ext x; rfl

theorem pair_chain_square : CoefficientRelativeSmall.subspaceMap R (excisedSubspace A Z) ≫
    CoefficientRelativeSmall.subspaceMap R (Zᶜ : Set X) =
    (chains R).map (TopCat.toSSet.map (pairInclusion A Z)) ≫ CoefficientRelativeSmall.subspaceMap R A := by
  change (chains R).map _ ≫ (chains R).map _ = (chains R).map _ ≫ (chains R).map _
  simp only [← Functor.map_comp, pair_square]

def excisionMap : CoefficientRelativeSmall.relativeChains R (excisedSubspace A Z) ⟶
    CoefficientRelativeSmall.relativeChains R A :=
  cokernel.map _ _ ((chains R).map (TopCat.toSSet.map (pairInclusion A Z)))
    (CoefficientRelativeSmall.subspaceMap R (Zᶜ : Set X)) (pair_chain_square R A Z)

theorem projection : cokernel.π (CoefficientRelativeSmall.subspaceMap R (excisedSubspace A Z)) ≫
    excisionMap R A Z = CoefficientRelativeSmall.subspaceMap R (Zᶜ : Set X) ≫
    cokernel.π (CoefficientRelativeSmall.subspaceMap R A) := cokernel.π_desc _ _ _

theorem projection_degree (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (excisedSubspace A Z))).f n ≫
    (excisionMap R A Z).f n = (CoefficientRelativeSmall.subspaceMap R (Zᶜ : Set X)).f n ≫
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R A)).f n :=
  congrArg (fun q => q.f n) (projection R A Z)

theorem complement_composite : (excisionComplementRangeChainsIso R Z).inv ≫
    (chains R).map (excisionComplementToAmbient A Z) ≫
    (excisionAmbientSmallChainsIso R A Z).hom ≫
    CoefficientSmallPath.coverSmallInclusion R (excisionCover A Z) =
    CoefficientRelativeSmall.subspaceMap R (Zᶜ : Set X) := by
  change (chains R).map _ ≫ (chains R).map _ ≫ (chains R).map _ ≫ (chains R).map _ = (chains R).map _
  simp only [← Functor.map_comp]
  congr 1
  exact excisionComplement_to_productionSSet A Z

theorem composite_eq : (smallIso R A Z).hom ≫
    CoefficientRelativeSmall.relativeMap R A (excisionCover A Z) = excisionMap R A Z := by
  apply (cancel_epi (cokernel.π (CoefficientRelativeSmall.subspaceMap R (excisedSubspace A Z)))).1
  have hp : cokernel.π (CoefficientRelativeSmall.restrictedMap R A (excisionCover A Z)) ≫
      CoefficientRelativeSmall.relativeMap R A (excisionCover A Z) =
      CoefficientSmallPath.coverSmallInclusion R (excisionCover A Z) ≫
      cokernel.π (CoefficientRelativeSmall.subspaceMap R A) := cokernel.π_desc _ _ _
  simp only [smallIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    excisionSourceRelativeIso, cokernel.mapIso_inv,
    CoefficientPushoutRelative.relativeIso, asIso_hom,
    CoefficientPushoutRelative.relativeMap, excisionTargetSmallRelativeIso, cokernel.mapIso_hom]
  simp only [cokernel.map, cokernel.π_desc_assoc, Category.assoc]
  rw [hp, projection]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ cokernel.π (CoefficientRelativeSmall.subspaceMap R A)) (complement_composite R A Z)



/-- All spaces and coefficients are Type 0; neither subspace must be inhabited. -/
def homologyIso (hZ : IsClosed Z) (hZA : Z ⊆ interior A) (n : ℕ) :
    (CoefficientRelativeSmall.relativeChains R (excisedSubspace A Z)).homology n ≅
    (CoefficientRelativeSmall.relativeChains R A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso (smallIso R A Z) ≪≫
  CoefficientRelativeSmall.comparisonIso R A (excisionCover A Z)
    (excisionCover_isOpen A Z hZ) (by rw [excisionCover_iUnion_eq_univ A Z hZA]) n

theorem homologyIso_hom (hZ : IsClosed Z) (hZA : Z ⊆ interior A) (n : ℕ) :
    (homologyIso R A Z hZ hZA n).hom = HomologicalComplex.homologyMap (excisionMap R A Z) n := by
  change HomologicalComplex.homologyMap (smallIso R A Z).hom n ≫
    HomologicalComplex.homologyMap (CoefficientRelativeSmall.relativeMap R A (excisionCover A Z)) n = _
  exact (HomologicalComplex.homologyMap_comp (smallIso R A Z).hom
    (CoefficientRelativeSmall.relativeMap R A (excisionCover A Z)) n).symm.trans
    (congrArg (fun f => HomologicalComplex.homologyMap f n) (composite_eq R A Z))

instance excision_isIso (hZ : IsClosed Z) (hZA : Z ⊆ interior A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (excisionMap R A Z) n) := by
  rw [← homologyIso_hom R A Z hZ hZA n]
  infer_instance

theorem inverse_left (hZ : IsClosed Z) (hZA : Z ⊆ interior A) (n : ℕ) :
    (homologyIso R A Z hZ hZA n).inv ≫ HomologicalComplex.homologyMap (excisionMap R A Z) n = 𝟙 _ := by
  rw [← homologyIso_hom R A Z hZ hZA n]; exact Iso.inv_hom_id _

theorem inverse_right (hZ : IsClosed Z) (hZA : Z ⊆ interior A) (n : ℕ) :
    HomologicalComplex.homologyMap (excisionMap R A Z) n ≫ (homologyIso R A Z hZ hZA n).inv = 𝟙 _ := by
  rw [← homologyIso_hom R A Z hZ hZA n]; exact Iso.hom_inv_id _

def integral_interval (n : ℕ) := homologyIso ℤ (Set.Ioo (-2 : ℝ) 2) (Set.Icc (-1 : ℝ) 1)
  isClosed_Icc (by rw [isOpen_Ioo.interior_eq]; intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) n

def rational_interval (n : ℕ) := homologyIso ℚ (Set.Ioo (-2 : ℝ) 2) (Set.Icc (-1 : ℝ) 1)
  isClosed_Icc (by rw [isOpen_Ioo.interior_eq]; intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) n

#print axioms excisionSourceChain_square
#print axioms excisionTargetChain_square
#print axioms smallIso
#print axioms projection_degree
#print axioms composite_eq
#print axioms homologyIso_hom
#print axioms excision_isIso
#print axioms inverse_left
#print axioms inverse_right
#print axioms integral_interval
#print axioms rational_interval
end ConstructionTargets.CoefficientExcision
