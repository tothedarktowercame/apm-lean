import ConstructionTargets.SingularHomologyConcrete
import ConstructionTargets.SingularSubdivision
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq

/-!
# Functorial maps of relative singular chains

This is the common algebraic input for excision and the sphere computations.
-/

noncomputable section

namespace ConstructionTargets.SingularExcision

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete

private abbrev ssetChains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

/-! ## Relative homology from absolute comparison squares -/

/-- The canonical short exact sequence ending in the cokernel of a monic
chain map. -/
noncomputable def cokernelShortComplex
    {K L : ChainComplex AddCommGrpCat ℕ} (f : K ⟶ L) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

theorem cokernelShortComplex_shortExact
    {K L : ChainComplex AddCommGrpCat ℕ} (f : K ⟶ L) [Mono f] :
    (cokernelShortComplex f).ShortExact := by
  apply ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
  · change Mono f
    infer_instance
  · change Epi (cokernel.π f)
    infer_instance

/-- A commuting square of chain maps induces the corresponding morphism of
cokernel short exact sequences. -/
noncomputable def cokernelSquareMap
    {K L K' L' : ChainComplex AddCommGrpCat ℕ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ f') :
    cokernelShortComplex f ⟶ cokernelShortComplex f' :=
  ShortComplex.homMk a b (cokernel.map f f' a b h) h.symm (by
    dsimp [cokernelShortComplex]
    symm
    apply cokernel.π_desc)

/-- Consumer-level relative comparison: if the two absolute vertical maps in
a square of monic chain maps induce isomorphisms in a degree and the adjacent
degree, then so does the induced map on relative cokernels. -/
theorem cokernelSquare_homologyMap_isIso
    {K L K' L' : ChainComplex AddCommGrpCat ℕ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ f') [Mono f] [Mono f'] (i : ℕ)
    (ha : IsIso (HomologicalComplex.homologyMap a i))
    (hb : IsIso (HomologicalComplex.homologyMap b i))
    (haPrev : ∀ j, (ComplexShape.down ℕ).Rel i j →
      IsIso (HomologicalComplex.homologyMap a j))
    (hbPrev : ∀ j, (ComplexShape.down ℕ).Rel i j →
      IsIso (HomologicalComplex.homologyMap b j)) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.map f f' a b h) i) := by
  let φ := cokernelSquareMap f f' a b h
  have hφ := HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ
    (cokernelShortComplex_shortExact f)
    (cokernelShortComplex_shortExact f') i
  apply hφ
  · change Epi (HomologicalComplex.homologyMap a i)
    letI := ha
    infer_instance
  · change IsIso (HomologicalComplex.homologyMap b i)
    exact hb
  · intro j hj
    change IsIso (HomologicalComplex.homologyMap a j)
    exact haPrev j hj
  · intro j hj
    change Mono (HomologicalComplex.homologyMap b j)
    letI := hbPrev j hj
    infer_instance

/-! ## Reassembly of free chains on a union -/

/-- Singular chains preserve pushouts of simplicial sets.  Degreewise this is
evaluation followed by the free abelian-group functor (`sigmaConst`), a left
adjoint. -/
noncomputable local instance ssetChains_preserves_pushouts :
    PreservesColimitsOfShape WalkingSpan ssetChains := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  dsimp [ssetChains, AlgebraicTopology.SSet.singularChainComplexFunctor]
  letI := (sigmaConstAdj (AddCommGrpCat.of ℤ)).leftAdjoint_preservesColimits
  change PreservesColimitsOfShape WalkingSpan
    ((evaluation SimplexCategoryᵒᵖ Type).obj
      (Opposite.op (SimplexCategory.mk n)) ⋙
      sigmaConst.obj (AddCommGrpCat.of ℤ))
  infer_instance

/-- The canonical inclusion from the intersection of two simplicial
subcomplexes into the left subcomplex. -/
def subcomplexIntersectionToLeft {S : SSet} (P Q : S.Subcomplex) :
    ((P ⊓ Q : S.Subcomplex) : SSet) ⟶ (P : SSet) :=
  SSet.Subcomplex.homOfLE (show P ⊓ Q ≤ P from inf_le_left)

/-- The canonical inclusion from the intersection of two simplicial
subcomplexes into the right subcomplex. -/
def subcomplexIntersectionToRight {S : SSet} (P Q : S.Subcomplex) :
    ((P ⊓ Q : S.Subcomplex) : SSet) ⟶ (Q : SSet) :=
  SSet.Subcomplex.homOfLE (show P ⊓ Q ≤ Q from inf_le_right)

/-- The canonical inclusion of the left simplicial subcomplex into a union. -/
def subcomplexLeftToUnion {S : SSet} (P Q : S.Subcomplex) :
    (P : SSet) ⟶ ((P ⊔ Q : S.Subcomplex) : SSet) :=
  SSet.Subcomplex.homOfLE (show P ≤ P ⊔ Q from le_sup_left)

/-- The canonical inclusion of the right simplicial subcomplex into a union. -/
def subcomplexRightToUnion {S : SSet} (P Q : S.Subcomplex) :
    (Q : SSet) ⟶ ((P ⊔ Q : S.Subcomplex) : SSet) :=
  SSet.Subcomplex.homOfLE (show Q ≤ P ⊔ Q from le_sup_right)

private abbrev interToLeft {S : SSet} (P Q : S.Subcomplex) :=
  subcomplexIntersectionToLeft P Q
private abbrev interToRight {S : SSet} (P Q : S.Subcomplex) :=
  subcomplexIntersectionToRight P Q
private abbrev leftToUnion {S : SSet} (P Q : S.Subcomplex) :=
  subcomplexLeftToUnion P Q
private abbrev rightToUnion {S : SSet} (P Q : S.Subcomplex) :=
  subcomplexRightToUnion P Q

/-- Inclusion of simplicial subcomplexes is degreewise monic after applying
free integral chains. -/
instance subcomplexChainsMap_component_mono {S : SSet}
    {P Q : S.Subcomplex} (h : P ≤ Q) (n : ℕ) :
    Mono ((ssetChains.map (SSet.Subcomplex.homOfLE h)).f n) := by
  dsimp [ssetChains, AlgebraicTopology.SSet.singularChainComplexFunctor]
  apply Limits.MonoCoprod.mono_map'_of_injective
  intro x y hxy
  apply Subtype.ext
  simpa only [SSet.Subcomplex.homOfLE_app_val] using
    congrArg Subtype.val hxy

/-- Inclusion of simplicial subcomplexes is monic on free integral chain
complexes. -/
instance subcomplexChainsMap_mono {S : SSet}
    {P Q : S.Subcomplex} (h : P ≤ Q) :
    Mono (ssetChains.map (SSet.Subcomplex.homOfLE h)) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦
    subcomplexChainsMap_component_mono h n

/-- Applying singular chains to the intersection/union square of two
simplicial subcomplexes gives a pushout square of chain complexes. -/
theorem subcomplexChains_isPushout {S : SSet} (P Q : S.Subcomplex) :
    IsPushout
      (ssetChains.map (interToLeft P Q))
      (ssetChains.map (interToRight P Q))
      (ssetChains.map (leftToUnion P Q))
      (ssetChains.map (rightToUnion P Q)) := by
  let sq : SSet.Subcomplex.BicartSq (P ⊓ Q) P Q (P ⊔ Q) :=
    { sup_eq := rfl, inf_eq := rfl }
  exact sq.isPushout.map ssetChains

/-- The canonical Mayer--Vietoris short complex of the chains on two
simplicial subcomplexes.  Its first map is the signed pair of inclusions from
the intersection and its second map reassembles chains in the union. -/
noncomputable def subcomplexMayerVietorisShortComplex {S : SSet}
    (P Q : S.Subcomplex) : ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  (subcomplexChains_isPushout P Q).shortComplex

/-- The chain-level Mayer--Vietoris sequence for two simplicial subcomplexes
is short exact. -/
theorem subcomplexMayerVietorisShortComplex_shortExact {S : SSet}
    (P Q : S.Subcomplex) :
    (subcomplexMayerVietorisShortComplex P Q).ShortExact := by
  let h := subcomplexChains_isPushout P Q
  change h.shortComplex.ShortExact
  apply ShortComplex.ShortExact.mk' h.exact_shortComplex
  · dsimp only [CommSq.shortComplex_f]
    change Mono (biprod.lift
      (ssetChains.map (SSet.Subcomplex.homOfLE
        (show P ⊓ Q ≤ P from inf_le_left))) _)
    letI : Mono (ssetChains.map (SSet.Subcomplex.homOfLE
        (show P ⊓ Q ≤ P from inf_le_left))) :=
      subcomplexChainsMap_mono (show P ⊓ Q ≤ P from inf_le_left)
    exact mono_of_mono_fac (biprod.lift_fst _ _)
  · exact h.epi_shortComplex_g

/-- The connecting morphism in the homology sequence of the canonical
subcomplex Mayer--Vietoris short complex. -/
noncomputable def subcomplexMayerVietorisConnecting {S : SSet}
    (P Q : S.Subcomplex) (n : ℕ) :
    ((subcomplexMayerVietorisShortComplex P Q).X₃.homology (n + 1)) ⟶
      ((subcomplexMayerVietorisShortComplex P Q).X₁.homology n) :=
  (subcomplexMayerVietorisShortComplex_shortExact P Q).δ (n + 1) n rfl

/-- Exactness at the intersection-homology term in the canonical
subcomplex Mayer--Vietoris sequence. -/
theorem subcomplexMayerVietoris_exact_intersection {S : SSet}
    (P Q : S.Subcomplex) (n : ℕ) :
    (ShortComplex.mk (subcomplexMayerVietorisConnecting P Q n)
      (HomologicalComplex.homologyMap
        (subcomplexMayerVietorisShortComplex P Q).f n)
      ((subcomplexMayerVietorisShortComplex_shortExact P Q).δ_comp
        (n + 1) n rfl)).Exact :=
  (subcomplexMayerVietorisShortComplex_shortExact P Q).homology_exact₁
    (n + 1) n rfl

/-- Exactness at the sum-of-pieces homology term in the canonical
subcomplex Mayer--Vietoris sequence. -/
theorem subcomplexMayerVietoris_exact_pieces {S : SSet}
    (P Q : S.Subcomplex) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (subcomplexMayerVietorisShortComplex P Q).f n)
      (HomologicalComplex.homologyMap
        (subcomplexMayerVietorisShortComplex P Q).g n)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        rw [(subcomplexMayerVietorisShortComplex P Q).zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  (subcomplexMayerVietorisShortComplex_shortExact P Q).homology_exact₂ n

/-- Exactness at the union-homology term in the canonical subcomplex
Mayer--Vietoris sequence. -/
theorem subcomplexMayerVietoris_exact_union {S : SSet}
    (P Q : S.Subcomplex) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (subcomplexMayerVietorisShortComplex P Q).g (n + 1))
      (subcomplexMayerVietorisConnecting P Q n)
      ((subcomplexMayerVietorisShortComplex_shortExact P Q).comp_δ
        (n + 1) n rfl)).Exact :=
  (subcomplexMayerVietorisShortComplex_shortExact P Q).homology_exact₃
    (n + 1) n rfl

noncomputable instance subcomplexUnionRelativeMap_isIso {S : SSet}
    (P Q : S.Subcomplex) :
    IsIso (cokernel.map
      (ssetChains.map (interToRight P Q))
      (ssetChains.map (leftToUnion P Q))
      (ssetChains.map (interToLeft P Q))
      (ssetChains.map (rightToUnion P Q))
      (subcomplexChains_isPushout P Q).flip.w) :=
  isIso_cokernel_map_of_isPushout (subcomplexChains_isPushout P Q).flip

/-- Any simplicial pushout square induces an isomorphism between the two
relative chain cokernels.  This is the presentation-independent form used by
the excision square. -/
noncomputable def ssetPushoutRelativeMap
    {W X Y Z : SSet} {f : W ⟶ X} {g : W ⟶ Y}
    {h : X ⟶ Z} {i : Y ⟶ Z} (sq : IsPushout f g h i) :
    cokernel (ssetChains.map g) ⟶ cokernel (ssetChains.map h) :=
  cokernel.map (ssetChains.map g) (ssetChains.map h)
      (ssetChains.map f) (ssetChains.map i)
      (sq.map ssetChains).flip.w

noncomputable instance ssetPushoutCokernelMap_isIso
    {W X Y Z : SSet} {f : W ⟶ X} {g : W ⟶ Y}
    {h : X ⟶ Z} {i : Y ⟶ Z} (sq : IsPushout f g h i) :
    IsIso (ssetPushoutRelativeMap sq) :=
  isIso_cokernel_map_of_isPushout (sq.map ssetChains).flip

/-- The relative-chain isomorphism induced by a simplicial pushout. -/
noncomputable def ssetPushoutRelativeIso
    {W X Y Z : SSet} {f : W ⟶ X} {g : W ⟶ Y}
    {h : X ⟶ Z} {i : Y ⟶ Z} (sq : IsPushout f g h i) :
    cokernel (ssetChains.map g) ≅ cokernel (ssetChains.map h) :=
  asIso (ssetPushoutRelativeMap sq)

/-- The free-chain second isomorphism theorem.  Modding the chains on `Q` by
those on `P ∩ Q` is canonically the same as modding the chains on `P ∪ Q` by
those on `P`.  This is the algebraic reassembly used by excision. -/
noncomputable def subcomplexUnionRelativeIso {S : SSet}
    (P Q : S.Subcomplex) :
    cokernel (ssetChains.map (interToRight P Q)) ≅
      cokernel (ssetChains.map (leftToUnion P Q)) :=
  asIso (cokernel.map
    (ssetChains.map (interToRight P Q))
    (ssetChains.map (leftToUnion P Q))
    (ssetChains.map (interToLeft P Q))
    (ssetChains.map (rightToUnion P Q))
    (subcomplexChains_isPushout P Q).flip.w)

/-! ## The cover used in excision -/

/-- The part of `A` remaining inside the complement of `Z`. -/
def excisedSubspace {X : Type} [TopologicalSpace X]
    (A Z : Set X) : Set (Zᶜ : Set X) :=
  Subtype.val ⁻¹' A

/-- The standard two-member cover used to excise `Z` from the pair `(X,A)`:
the interior of `A` and the complement of `Z`. -/
def excisionCover {X : Type} [TopologicalSpace X] (A Z : Set X) : Bool → Set X
  | false => interior A
  | true => Zᶜ

theorem excisionCover_isOpen {X : Type} [TopologicalSpace X]
    (A Z : Set X) (hZclosed : IsClosed Z) (b : Bool) :
    IsOpen (excisionCover A Z b) := by
  cases b
  · exact isOpen_interior
  · exact hZclosed.isOpen_compl

theorem excisionCover_iUnion_eq_univ {X : Type} [TopologicalSpace X]
    (A Z : Set X) (hZ : Z ⊆ interior A) :
    ⋃ b, excisionCover A Z b = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ Z
  · exact Set.mem_iUnion.2 ⟨false, hZ hx⟩
  · exact Set.mem_iUnion.2 ⟨true, hx⟩

/-- Restrict every member of a cover of `X` to a subspace `A`. -/
def restrictedCover {X α : Type} [TopologicalSpace X]
    (A : Set X) (U : α → Set X) (a : α) : Set A :=
  Subtype.val ⁻¹' U a

theorem restrictedCover_isOpen {X α : Type} [TopologicalSpace X]
    (A : Set X) (U : α → Set X) (hU : ∀ a, IsOpen (U a)) (a : α) :
    IsOpen (restrictedCover A U a) :=
  (hU a).preimage continuous_subtype_val

theorem restrictedCover_iUnion_eq_univ {X α : Type} [TopologicalSpace X]
    (A : Set X) (U : α → Set X) (hU : ⋃ a, U a = Set.univ) :
    ⋃ a, restrictedCover A U a = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  have hx : x.1 ∈ ⋃ a, U a := by rw [hU]; trivial
  simpa only [Set.mem_iUnion, restrictedCover, Set.mem_preimage] using hx

/-- A cover containing the whole space has no small-chain restriction. -/
theorem coverSmallSSet_eq_top_of_eq_univ
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (a : α)
    (ha : U a = Set.univ) :
    SingularSubdivision.coverSmallSSet U = ⊤ := by
  apply top_unique
  intro n σ hσ
  let f := (TopCat.toSSetObjEquiv (TopCat.of X) n).toFun σ
  have hf : ∀ x, f x ∈ U a := by
    intro x
    rw [ha]
    trivial
  let τ : C(stdSimplex ℝ (Fin (n.unop.len + 1)), U a) :=
    ⟨fun x ↦ ⟨f x, hf x⟩, f.continuous.subtype_mk hf⟩
  have hmapped :
      (TopCat.toSSet.map (SingularSubdivision.coverSubspaceInclusion U a)).app n
          ((TopCat.toSSetObjEquiv (TopCat.of (U a)) n).symm τ) = σ := by
    apply (TopCat.toSSetObjEquiv (TopCat.of X) n).injective
    ext x
    rfl
  apply (le_iSup (fun b => SSet.Subcomplex.range
    (TopCat.toSSet.map (SingularSubdivision.coverSubspaceInclusion U b))) a)
  exact ⟨(TopCat.toSSetObjEquiv (TopCat.of (U a)) n).symm τ, hmapped⟩

/-- When the small simplicial set is top, its chain complex is canonically the
production singular chain complex. -/
noncomputable def subcomplexIsoOfEqTop {S : SSet} (P : S.Subcomplex)
    (h : P = ⊤) : (P : SSet) ≅ S :=
  eqToIso (congrArg (fun Q : S.Subcomplex ↦ (Q : SSet)) h) ≪≫
    SSet.Subcomplex.topIso _

theorem subcomplexIsoOfEqTop_hom {S : SSet} (P : S.Subcomplex)
    (h : P = ⊤) : (subcomplexIsoOfEqTop P h).hom = P.ι := by
  subst P
  rfl

noncomputable def coverSmallSSetIsoOfEqTop
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (h : SingularSubdivision.coverSmallSSet U = ⊤) :
    (SingularSubdivision.coverSmallSSet U : SSet) ≅
      TopCat.toSSet.obj (TopCat.of X) :=
  subcomplexIsoOfEqTop _ h

theorem coverSmallSSetIsoOfEqTop_hom
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (h : SingularSubdivision.coverSmallSSet U = ⊤) :
    (coverSmallSSetIsoOfEqTop U h).hom =
      (SingularSubdivision.coverSmallSSet U).ι := by
  exact subcomplexIsoOfEqTop_hom _ h

noncomputable def coverSmallChainsIsoOfEqTop
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (h : SingularSubdivision.coverSmallSSet U = ⊤) :
    SingularSubdivision.coverSmallChains U ≅ SingularChains (TopCat.of X) :=
  ssetChains.mapIso (coverSmallSSetIsoOfEqTop U h)

theorem coverSmallChainsIsoOfEqTop_hom
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (h : SingularSubdivision.coverSmallSSet U = ⊤) :
    (coverSmallChainsIsoOfEqTop U h).hom =
      SingularSubdivision.coverSmallChains.ι U := by
  dsimp [coverSmallChainsIsoOfEqTop,
    SingularSubdivision.coverSmallChains.ι]
  rw [coverSmallSSetIsoOfEqTop_hom]

theorem restrictedExcisionCover_complement_true_eq_univ
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    restrictedCover (Zᶜ : Set X) (excisionCover A Z) true = Set.univ := by
  ext x
  simp [restrictedCover, excisionCover]

/-- On the complement of the excised set, the excision cover-small simplicial
set is the entire singular simplicial set. -/
theorem restrictedExcisionCover_complement_small_eq_top
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    SingularSubdivision.coverSmallSSet
      (restrictedCover (Zᶜ : Set X) (excisionCover A Z)) = ⊤ :=
  coverSmallSSet_eq_top_of_eq_univ _ true
    (restrictedExcisionCover_complement_true_eq_univ A Z)

theorem restrictedExcisionCover_excised_true_eq_univ
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    restrictedCover (excisedSubspace A Z)
      (restrictedCover (Zᶜ : Set X) (excisionCover A Z)) true =
      Set.univ := by
  ext x
  simp [restrictedCover, excisionCover]

theorem restrictedExcisionCover_excised_small_eq_top
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    SingularSubdivision.coverSmallSSet
      (restrictedCover (excisedSubspace A Z)
        (restrictedCover (Zᶜ : Set X) (excisionCover A Z))) = ⊤ :=
  coverSmallSSet_eq_top_of_eq_univ _ true
    (restrictedExcisionCover_excised_true_eq_univ A Z)

/-- Both absolute complexes on the excised side of the cover-small square are
already the full production singular-chain complexes. -/
noncomputable def excisionComplementSmallChainsIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    SingularSubdivision.coverSmallChains
        (restrictedCover (Zᶜ : Set X) (excisionCover A Z)) ≅
      SingularChains (TopCat.of (Zᶜ : Set X)) :=
  coverSmallChainsIsoOfEqTop _
    (restrictedExcisionCover_complement_small_eq_top A Z)

noncomputable def excisionIntersectionSmallChainsIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    SingularSubdivision.coverSmallChains
        (restrictedCover (excisedSubspace A Z)
          (restrictedCover (Zᶜ : Set X) (excisionCover A Z))) ≅
      SingularChains (TopCat.of (excisedSubspace A Z)) :=
  coverSmallChainsIsoOfEqTop _
    (restrictedExcisionCover_excised_small_eq_top A Z)

/-- For a two-member cover, the small singular simplicial set is literally
the join of the two simplicial ranges.  Keeping this equality named avoids
re-expanding a `Bool`-indexed supremum in the excision pushout. -/
theorem coverSmallSSet_bool_eq_sup
    {X : Type} [TopologicalSpace X] (U : Bool → Set X) :
    SingularSubdivision.coverSmallSSet U =
      SSet.Subcomplex.range (TopCat.toSSet.map
        (SingularSubdivision.coverSubspaceInclusion U true)) ⊔
      SSet.Subcomplex.range (TopCat.toSSet.map
        (SingularSubdivision.coverSubspaceInclusion U false)) := by
  simp only [SingularSubdivision.coverSmallSSet, iSup_bool_eq]

/-- The ambient small simplicial set for the excision cover is the union of
the complement range and the interior range. -/
theorem excisionCoverSmallSSet_eq_sup
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    SingularSubdivision.coverSmallSSet (excisionCover A Z) =
      SSet.Subcomplex.range (TopCat.toSSet.map
        (SingularSubdivision.coverSubspaceInclusion
          (excisionCover A Z) true)) ⊔
      SSet.Subcomplex.range (TopCat.toSSet.map
        (SingularSubdivision.coverSubspaceInclusion
          (excisionCover A Z) false)) :=
  coverSmallSSet_bool_eq_sup _

/-- The simplicial subcomplex of ambient singular simplices which factor
through a specified topological subspace. -/
def ambientSubspaceRange {X : Type} [TopologicalSpace X] (A : Set X) :
    (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (subspaceInclusion A))

noncomputable instance singularSubspaceSSetMap_mono
    {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (TopCat.toSSet.map (subspaceInclusion A)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y h
  apply (TopCat.toSSetObjEquiv (TopCat.of A) n).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  have hf := congrArg
    (fun σ ↦ (TopCat.toSSetObjEquiv (TopCat.of X) n).toFun σ) h
  exact DFunLike.congr_fun hf t

/-- Simplices factoring through both subspaces are exactly the simplices
factoring through their intersection. -/
theorem ambientSubspaceRange_inf
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    ambientSubspaceRange A ⊓ ambientSubspaceRange B =
      ambientSubspaceRange (A ∩ B) := by
  ext n σ
  constructor
  · rintro ⟨⟨σA, hA⟩, ⟨σB, hB⟩⟩
    let f := (TopCat.toSSetObjEquiv (TopCat.of X) n).toFun σ
    have hfA : ∀ x, f x ∈ A := by
      intro x
      have := congrArg
        (fun τ ↦ (TopCat.toSSetObjEquiv (TopCat.of X) n).toFun τ x) hA
      change
        (((TopCat.toSSetObjEquiv (TopCat.of A) n).toFun σA) x).1 = f x at this
      rw [← this]
      exact (((TopCat.toSSetObjEquiv (TopCat.of A) n).toFun σA) x).2
    have hfB : ∀ x, f x ∈ B := by
      intro x
      have := congrArg
        (fun τ ↦ (TopCat.toSSetObjEquiv (TopCat.of X) n).toFun τ x) hB
      change
        (((TopCat.toSSetObjEquiv (TopCat.of B) n).toFun σB) x).1 = f x at this
      rw [← this]
      exact (((TopCat.toSSetObjEquiv (TopCat.of B) n).toFun σB) x).2
    let τ : C(stdSimplex ℝ (Fin (n.unop.len + 1)), (A ∩ B : Set X)) :=
      ⟨fun x ↦ ⟨f x, hfA x, hfB x⟩,
        f.continuous.subtype_mk (fun x ↦ ⟨hfA x, hfB x⟩)⟩
    refine ⟨(TopCat.toSSetObjEquiv (TopCat.of (A ∩ B : Set X)) n).symm τ, ?_⟩
    apply (TopCat.toSSetObjEquiv (TopCat.of X) n).injective
    ext x
    rfl
  · rintro ⟨σAB, hAB⟩
    let incA : TopCat.of (A ∩ B : Set X) ⟶ TopCat.of A :=
      TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.1⟩,
        continuous_subtype_val.subtype_mk _⟩
    let incB : TopCat.of (A ∩ B : Set X) ⟶ TopCat.of B :=
      TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.2⟩,
        continuous_subtype_val.subtype_mk _⟩
    constructor
    · refine ⟨(TopCat.toSSet.map incA).app n σAB, ?_⟩
      have hc : TopCat.toSSet.map incA ≫
          TopCat.toSSet.map (subspaceInclusion A) =
          TopCat.toSSet.map (subspaceInclusion (A ∩ B)) := by
        rw [← TopCat.toSSet.map_comp]
        congr 1
      simpa only [NatTrans.comp_app, Function.comp_apply] using
        (congrArg (fun k ↦ k.app n σAB) hc).trans hAB
    · refine ⟨(TopCat.toSSet.map incB).app n σAB, ?_⟩
      have hc : TopCat.toSSet.map incB ≫
          TopCat.toSSet.map (subspaceInclusion B) =
          TopCat.toSSet.map (subspaceInclusion (A ∩ B)) := by
        rw [← TopCat.toSSet.map_comp]
        congr 1
      simpa only [NatTrans.comp_app, Function.comp_apply] using
        (congrArg (fun k ↦ k.app n σAB) hc).trans hAB

private def restrictedCoverMemberMap {X α : Type} [TopologicalSpace X]
    (A : Set X) (U : α → Set X) (a : α) :
    TopCat.of (restrictedCover A U a) ⟶ TopCat.of (U a) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

private theorem restrictedCoverMemberMap_comp {X α : Type}
    [TopologicalSpace X] (A : Set X) (U : α → Set X) (a : α) :
    restrictedCoverMemberMap A U a ≫
        SingularSubdivision.coverSubspaceInclusion U a =
      SingularSubdivision.coverSubspaceInclusion (restrictedCover A U) a ≫
        subspaceInclusion A := by
  ext x
  rfl

/-- Viewed in the ambient singular simplicial set, one member of a cover
restricted to `A` is exactly the intersection of the two ambient subspace
ranges. -/
theorem restrictedCoverMember_ambientRange
    {X α : Type} [TopologicalSpace X]
    (A : Set X) (U : α → Set X) (a : α) :
    SSet.Subcomplex.range (TopCat.toSSet.map
      (SingularSubdivision.coverSubspaceInclusion (restrictedCover A U) a ≫
        subspaceInclusion A)) =
      ambientSubspaceRange A ⊓ ambientSubspaceRange (U a) := by
  rw [ambientSubspaceRange_inf]
  let toInter : TopCat.of (restrictedCover A U a) ⟶
      TopCat.of (A ∩ U a : Set X) :=
    TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.1.2, x.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let fromInter : TopCat.of (A ∩ U a : Set X) ⟶
      TopCat.of (restrictedCover A U a) :=
    TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  apply le_antisymm
  · rw [show SingularSubdivision.coverSubspaceInclusion
          (restrictedCover A U) a ≫ subspaceInclusion A =
        toInter ≫ subspaceInclusion (A ∩ U a) by ext x; rfl,
      TopCat.toSSet.map_comp, SSet.Subcomplex.range_comp]
    exact SSet.Subcomplex.image_le_range _ _
  · change SSet.Subcomplex.range
      (TopCat.toSSet.map (subspaceInclusion (A ∩ U a))) ≤ _
    rw [show subspaceInclusion (A ∩ U a) =
        fromInter ≫ SingularSubdivision.coverSubspaceInclusion
          (restrictedCover A U) a ≫ subspaceInclusion A by ext x; rfl,
      TopCat.toSSet.map_comp, TopCat.toSSet.map_comp,
      SSet.Subcomplex.range_comp]
    exact SSet.Subcomplex.image_le_range _ _

/-- The image in ambient singular simplices of all chains subordinate to the
restricted cover is the join of the intersections with the ambient subspace
range. -/
theorem restrictedCoverSmallSSet_image
    {X α : Type} [TopologicalSpace X]
    (A : Set X) (U : α → Set X) :
    (SingularSubdivision.coverSmallSSet (restrictedCover A U)).image
        (TopCat.toSSet.map (subspaceInclusion A)) =
      ⨆ a, ambientSubspaceRange A ⊓
        SSet.Subcomplex.range (TopCat.toSSet.map
          (SingularSubdivision.coverSubspaceInclusion U a)) := by
  rw [SingularSubdivision.coverSmallSSet, SSet.Subcomplex.image_iSup]
  apply iSup_congr
  intro a
  rw [← SSet.Subcomplex.range_comp, ← TopCat.toSSet.map_comp]
  exact restrictedCoverMember_ambientRange A U a

theorem ambientSubspaceRange_mono
    {X : Type} [TopologicalSpace X] {A B : Set X} (h : A ⊆ B) :
    ambientSubspaceRange A ≤ ambientSubspaceRange B := by
  let inc : TopCat.of A ⟶ TopCat.of B :=
    TopCat.ofHom ⟨fun x ↦ ⟨x.1, h x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  rw [show ambientSubspaceRange A = SSet.Subcomplex.range
      (TopCat.toSSet.map inc ≫ TopCat.toSSet.map (subspaceInclusion B)) by
    dsimp [ambientSubspaceRange]
    rw [← TopCat.toSSet.map_comp]
    congr 1,
    SSet.Subcomplex.range_comp]
  exact SSet.Subcomplex.image_le_range _ _

/-- In the ambient singular simplicial set, the restricted small part of `A`
for the excision cover is the union of the interior part and the part of `A`
remaining in the complement of `Z`. -/
theorem restrictedExcisionCoverSmallSSet_image
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (SingularSubdivision.coverSmallSSet
        (restrictedCover A (excisionCover A Z))).image
        (TopCat.toSSet.map (subspaceInclusion A)) =
      (ambientSubspaceRange A ⊓ ambientSubspaceRange Zᶜ) ⊔
        ambientSubspaceRange (interior A) := by
  rw [restrictedCoverSmallSSet_image, iSup_bool_eq]
  change (ambientSubspaceRange A ⊓ ambientSubspaceRange Zᶜ) ⊔
      (ambientSubspaceRange A ⊓ ambientSubspaceRange (interior A)) = _
  rw [inf_eq_right.mpr (ambientSubspaceRange_mono interior_subset)]

private abbrev excisionComplementSC
    {X : Type} [TopologicalSpace X] (Z : Set X) :=
  ambientSubspaceRange (Zᶜ : Set X)

private abbrev excisionIntersectionSC
    {X : Type} [TopologicalSpace X] (A Z : Set X) :=
  ambientSubspaceRange A ⊓ excisionComplementSC Z

private abbrev excisionRestrictedSC
    {X : Type} [TopologicalSpace X] (A Z : Set X) :=
  excisionIntersectionSC A Z ⊔ ambientSubspaceRange (interior A)

private abbrev excisionAmbientSC
    {X : Type} [TopologicalSpace X] (A Z : Set X) :=
  excisionComplementSC Z ⊔ ambientSubspaceRange (interior A)

/-- The four simplicial subcomplexes underlying excision form a bicartesian
lattice square.  This is the geometric core: the only use of the excision
hypothesis is that the interior range lies in the `A` range. -/
theorem excisionSubcomplex_bicartSq
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    SSet.Subcomplex.BicartSq
      (excisionIntersectionSC A Z) (excisionComplementSC Z)
      (excisionRestrictedSC A Z) (excisionAmbientSC A Z) := by
  have hW : excisionIntersectionSC A Z ≤ excisionComplementSC Z :=
    inf_le_right
  have hI : ambientSubspaceRange (interior A) ≤ ambientSubspaceRange A :=
    ambientSubspaceRange_mono interior_subset
  constructor
  · calc
      excisionComplementSC Z ⊔ excisionRestrictedSC A Z =
          (excisionComplementSC Z ⊔ excisionIntersectionSC A Z) ⊔
            ambientSubspaceRange (interior A) := by rw [sup_assoc]
      _ = excisionAmbientSC A Z := by rw [sup_eq_left.mpr hW]
  · change excisionComplementSC Z ⊓
        (excisionIntersectionSC A Z ⊔ ambientSubspaceRange (interior A)) =
      excisionIntersectionSC A Z
    ext n σ
    constructor
    · rintro ⟨hQ, hW' | hInt⟩
      · exact hW'
      · exact ⟨hI n hInt, hQ⟩
    · intro hW'
      exact ⟨hW'.2, Or.inl hW'⟩

/-- The corresponding square of simplicial sets is a pushout. -/
noncomputable def excisionSubcomplex_isPushout
    {X : Type} [TopologicalSpace X] (A Z : Set X) :=
  (excisionSubcomplex_bicartSq A Z).isPushout

/-- The chain-level excision isomorphism for the four ambient simplicial
subcomplexes.  Its source is complement chains modulo the intersection and
its target is cover-small ambient chains modulo the restricted small part. -/
noncomputable def excisionSmallRelativeIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :=
  subcomplexUnionRelativeIso
    (excisionRestrictedSC A Z) (excisionComplementSC Z)

/-- Chains on the range of a monomorphism are canonically chains on its
domain. -/
noncomputable def rangeChainsIso {S T : SSet} (f : S ⟶ T) [Mono f] :
    ssetChains.obj (SSet.Subcomplex.range f : SSet) ≅ ssetChains.obj S :=
  ssetChains.mapIso (asIso (Subfunctor.toRange f)).symm

theorem rangeIso_hom_comp {S T : SSet} (f : S ⟶ T) [Mono f] :
    (asIso (Subfunctor.toRange f)).inv ≫ f =
      (SSet.Subcomplex.range f).ι := by
  apply (cancel_epi (Subfunctor.toRange f)).1
  simp

/-- The actual inclusion between topological subspaces determined by a set
inclusion. -/
def topologicalSubspaceInclusion {X : Type} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, h x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The inclusion between ambient range subcomplexes determined by a set
inclusion. -/
def ambientSubspaceRangeInclusion {X : Type} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) :
    (ambientSubspaceRange A : SSet) ⟶ (ambientSubspaceRange B : SSet) :=
  SSet.Subcomplex.homOfLE (ambientSubspaceRange_mono h)

/-- The range presentation of subspace singular chains. -/
noncomputable def ambientSubspaceRangeChainsIso
    {X : Type} [TopologicalSpace X] (A : Set X) :
    ssetChains.obj (ambientSubspaceRange A : SSet) ≅
      SingularChains (TopCat.of A) :=
  rangeChainsIso (TopCat.toSSet.map (subspaceInclusion A))

/-- Factoring through the range and then including into the larger range is
compatible with the actual inclusion of topological subspaces. -/
theorem ambientSubspaceRangeInclusion_square
    {X : Type} [TopologicalSpace X] {A B : Set X} (h : A ⊆ B) :
    (asIso (Subfunctor.toRange
          (TopCat.toSSet.map (subspaceInclusion A)))).inv ≫
        TopCat.toSSet.map (topologicalSubspaceInclusion h) =
      ambientSubspaceRangeInclusion h ≫
        (asIso (Subfunctor.toRange
          (TopCat.toSSet.map (subspaceInclusion B)))).inv := by
  apply (cancel_mono (TopCat.toSSet.map (subspaceInclusion B))).1
  calc
    _ = (asIso (Subfunctor.toRange
          (TopCat.toSSet.map (subspaceInclusion A)))).inv ≫
        (TopCat.toSSet.map (topologicalSubspaceInclusion h) ≫
          TopCat.toSSet.map (subspaceInclusion B)) := by simp only [Category.assoc]
    _ = (asIso (Subfunctor.toRange
          (TopCat.toSSet.map (subspaceInclusion A)))).inv ≫
        TopCat.toSSet.map (subspaceInclusion A) := by
          rw [← TopCat.toSSet.map_comp]
          rfl
    _ = (ambientSubspaceRange A).ι := rangeIso_hom_comp _
    _ = ambientSubspaceRangeInclusion h ≫
        (ambientSubspaceRange B).ι := rfl
    _ = (ambientSubspaceRangeInclusion h ≫
          (asIso (Subfunctor.toRange
            (TopCat.toSSet.map (subspaceInclusion B)))).inv) ≫
        TopCat.toSSet.map (subspaceInclusion B) := by
          rw [Category.assoc]
          exact congrArg (fun k ↦ ambientSubspaceRangeInclusion h ≫ k)
            (rangeIso_hom_comp
              (TopCat.toSSet.map (subspaceInclusion B))).symm

/-- Chain-level naturality of the range presentation with respect to an
actual subspace inclusion. -/
theorem ambientSubspaceRangeChainsIso_naturality
    {X : Type} [TopologicalSpace X] {A B : Set X} (h : A ⊆ B) :
    (ambientSubspaceRangeChainsIso A).hom ≫
        ssetChains.map (TopCat.toSSet.map (topologicalSubspaceInclusion h)) =
      ssetChains.map (ambientSubspaceRangeInclusion h) ≫
        (ambientSubspaceRangeChainsIso B).hom := by
  change ssetChains.map _ ≫ ssetChains.map _ =
    ssetChains.map _ ≫ ssetChains.map _
  simpa only [← Functor.map_comp] using
    congrArg ssetChains.map (ambientSubspaceRangeInclusion_square h)

/-- Homology-level naturality of the range presentation with respect to an
actual subspace inclusion. -/
theorem ambientSubspaceRangeHomologyIso_naturality
    {X : Type} [TopologicalSpace X] {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    HomologicalComplex.homologyMap
          (ambientSubspaceRangeChainsIso A).hom n ≫
        HomologicalComplex.homologyMap
          (ssetChains.map
            (TopCat.toSSet.map (topologicalSubspaceInclusion h))) n =
      HomologicalComplex.homologyMap
          (ssetChains.map (ambientSubspaceRangeInclusion h)) n ≫
        HomologicalComplex.homologyMap
          (ambientSubspaceRangeChainsIso B).hom n := by
  calc
    _ = HomologicalComplex.homologyMap
        ((ambientSubspaceRangeChainsIso A).hom ≫
          ssetChains.map
            (TopCat.toSSet.map (topologicalSubspaceInclusion h))) n :=
      (HomologicalComplex.homologyMap_comp _ _ _).symm
    _ = HomologicalComplex.homologyMap
        (ssetChains.map (ambientSubspaceRangeInclusion h) ≫
          (ambientSubspaceRangeChainsIso B).hom) n := by
      rw [ambientSubspaceRangeChainsIso_naturality]
      rfl
    _ = _ := HomologicalComplex.homologyMap_comp _ _ _

/-- Naturality for the production inclusion `A ∩ B ⟶ A`. -/
theorem ambientIntersectionRangeToLeft_naturality
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (ambientSubspaceRangeChainsIso (A ∩ B)).hom ≫
        ssetChains.map (TopCat.toSSet.map
          (topologicalSubspaceInclusion (Set.inter_subset_left))) =
      ssetChains.map
          (ambientSubspaceRangeInclusion (Set.inter_subset_left)) ≫
        (ambientSubspaceRangeChainsIso A).hom :=
  ambientSubspaceRangeChainsIso_naturality Set.inter_subset_left

/-- Naturality for the production inclusion `A ∩ B ⟶ B`. -/
theorem ambientIntersectionRangeToRight_naturality
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (ambientSubspaceRangeChainsIso (A ∩ B)).hom ≫
        ssetChains.map (TopCat.toSSet.map
          (topologicalSubspaceInclusion (Set.inter_subset_right))) =
      ssetChains.map
          (ambientSubspaceRangeInclusion (Set.inter_subset_right)) ≫
        (ambientSubspaceRangeChainsIso B).hom :=
  ambientSubspaceRangeChainsIso_naturality Set.inter_subset_right

/-- Naturality for the production inclusion `A ⟶ A ∪ B`. -/
theorem ambientLeftRangeToUnion_naturality
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (ambientSubspaceRangeChainsIso A).hom ≫
        ssetChains.map (TopCat.toSSet.map
          (topologicalSubspaceInclusion (Set.subset_union_left))) =
      ssetChains.map
          (ambientSubspaceRangeInclusion (Set.subset_union_left)) ≫
        (ambientSubspaceRangeChainsIso (A ∪ B)).hom :=
  ambientSubspaceRangeChainsIso_naturality Set.subset_union_left

/-- Naturality for the production inclusion `B ⟶ A ∪ B`. -/
theorem ambientRightRangeToUnion_naturality
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (ambientSubspaceRangeChainsIso B).hom ≫
        ssetChains.map (TopCat.toSSet.map
          (topologicalSubspaceInclusion (Set.subset_union_right))) =
      ssetChains.map
          (ambientSubspaceRangeInclusion (Set.subset_union_right)) ≫
        (ambientSubspaceRangeChainsIso (A ∪ B)).hom :=
  ambientSubspaceRangeChainsIso_naturality Set.subset_union_right

/-- Inclusion of one member's ambient range into the simplicial subcomplex
subordinate to the whole cover. -/
def coverMemberRangeInclusion
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (a : α) :
    (ambientSubspaceRange (U a) : SSet) ⟶
      (SingularSubdivision.coverSmallSSet U : SSet) :=
  SSet.Subcomplex.homOfLE (by
    apply le_iSup_of_le a
    rfl)

/-- The range-to-cover-small inclusion followed by the production inclusion
is the actual inclusion of the cover member into the ambient space. -/
theorem coverMemberRangeInclusion_square
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (a : α) :
    (asIso (Subfunctor.toRange
        (TopCat.toSSet.map (subspaceInclusion (U a))))).inv ≫
        TopCat.toSSet.map
          (SingularSubdivision.coverSubspaceInclusion U a) =
      coverMemberRangeInclusion U a ≫
        (SingularSubdivision.coverSmallSSet U).ι := by
  change (asIso (Subfunctor.toRange
      (TopCat.toSSet.map (subspaceInclusion (U a))))).inv ≫
      TopCat.toSSet.map (subspaceInclusion (U a)) = _
  rw [rangeIso_hom_comp]
  rfl

/-- Chain-level naturality of the cover-small comparison on each cover
member. -/
theorem coverMemberRangeChainsIso_naturality
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (a : α) :
    (ambientSubspaceRangeChainsIso (U a)).hom ≫
        ssetChains.map (TopCat.toSSet.map
          (SingularSubdivision.coverSubspaceInclusion U a)) =
      ssetChains.map (coverMemberRangeInclusion U a) ≫
        SingularSubdivision.coverSmallChains.ι U := by
  change ssetChains.map _ ≫ ssetChains.map _ =
    ssetChains.map _ ≫ ssetChains.map _
  simpa only [← Functor.map_comp] using congrArg ssetChains.map
    (coverMemberRangeInclusion_square U a)

/-- Homology-level naturality of the cover-small comparison on each cover
member. -/
theorem coverMemberRangeHomologyIso_naturality
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (a : α) (n : ℕ) :
    HomologicalComplex.homologyMap
          (ambientSubspaceRangeChainsIso (U a)).hom n ≫
        HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map
            (SingularSubdivision.coverSubspaceInclusion U a))) n =
      HomologicalComplex.homologyMap
          (ssetChains.map (coverMemberRangeInclusion U a)) n ≫
        HomologicalComplex.homologyMap
          (SingularSubdivision.coverSmallChains.ι U) n := by
  calc
    _ = HomologicalComplex.homologyMap
        ((ambientSubspaceRangeChainsIso (U a)).hom ≫
          ssetChains.map (TopCat.toSSet.map
            (SingularSubdivision.coverSubspaceInclusion U a))) n :=
      (HomologicalComplex.homologyMap_comp _ _ _).symm
    _ = HomologicalComplex.homologyMap
        (ssetChains.map (coverMemberRangeInclusion U a) ≫
          SingularSubdivision.coverSmallChains.ι U) n := by
      rw [coverMemberRangeChainsIso_naturality]
      rfl
    _ = _ := HomologicalComplex.homologyMap_comp _ _ _

theorem eqToIso_subcomplex_hom_comp_ι {S : SSet}
    (P Q : S.Subcomplex) (h : P = Q) :
    (eqToIso (congrArg (fun R : S.Subcomplex ↦ (R : SSet)) h)).hom ≫ Q.ι =
      P.ι := by
  subst Q
  rfl

theorem excisionCoverSmallSSet_eq_ambientSC
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    SingularSubdivision.coverSmallSSet (excisionCover A Z) =
      excisionAmbientSC A Z := by
  exact excisionCoverSmallSSet_eq_sup A Z

theorem restrictedExcisionCoverSmallSSet_image_eq_restrictedSC
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (SingularSubdivision.coverSmallSSet
        (restrictedCover A (excisionCover A Z))).image
        (TopCat.toSSet.map (subspaceInclusion A)) =
      excisionRestrictedSC A Z :=
  restrictedExcisionCoverSmallSSet_image A Z

private def restrictedExcisionSSetMap
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (SingularSubdivision.coverSmallSSet
        (restrictedCover A (excisionCover A Z)) : SSet) ⟶
      TopCat.toSSet.obj (TopCat.of X) :=
  (SingularSubdivision.coverSmallSSet
      (restrictedCover A (excisionCover A Z))).ι ≫
    TopCat.toSSet.map (subspaceInclusion A)

noncomputable instance restrictedExcisionSSetMap_mono
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    Mono (restrictedExcisionSSetMap A Z) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y h
  change (TopCat.toSSet.map (subspaceInclusion A)).app n x.1 =
    (TopCat.toSSet.map (subspaceInclusion A)).app n y.1 at h
  apply Subtype.ext
  apply (TopCat.toSSetObjEquiv (TopCat.of A) n).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  have hf := congrArg
    (fun σ ↦ (TopCat.toSSetObjEquiv (TopCat.of X) n).toFun σ) h
  exact DFunLike.congr_fun hf t

/-- The two named target vertices of the excision square are exactly the
cover-small chain complexes used by the small-chain comparison. -/
noncomputable def excisionAmbientSmallSSetIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionAmbientSC A Z : SSet) ≅
      (SingularSubdivision.coverSmallSSet (excisionCover A Z) : SSet) :=
  eqToIso (congrArg
    (fun P : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex ↦ (P : SSet))
    (excisionCoverSmallSSet_eq_ambientSC A Z).symm)

noncomputable def excisionRestrictedSmallSSetIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionRestrictedSC A Z : SSet) ≅
      (SingularSubdivision.coverSmallSSet
        (restrictedCover A (excisionCover A Z)) : SSet) :=
  eqToIso (congrArg
      (fun P : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex ↦ (P : SSet))
      (by
        rw [← restrictedExcisionCoverSmallSSet_image_eq_restrictedSC A Z,
          SSet.Subcomplex.image_eq_range]
        rfl)) ≪≫
    (asIso (Subfunctor.toRange (restrictedExcisionSSetMap A Z))).symm

noncomputable def excisionAmbientSmallChainsIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    ssetChains.obj (excisionAmbientSC A Z : SSet) ≅
      SingularSubdivision.coverSmallChains (excisionCover A Z) :=
  ssetChains.mapIso (excisionAmbientSmallSSetIso A Z)

noncomputable def excisionRestrictedSmallChainsIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    ssetChains.obj (excisionRestrictedSC A Z : SSet) ≅
      SingularSubdivision.coverSmallChains
        (restrictedCover A (excisionCover A Z)) :=
  ssetChains.mapIso (excisionRestrictedSmallSSetIso A Z)

private def excisionRestrictedToAmbient
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionRestrictedSC A Z : SSet) ⟶
      (excisionAmbientSC A Z : SSet) :=
  SSet.Subcomplex.homOfLE (excisionSubcomplex_bicartSq A Z).le₃₄

@[reassoc] theorem excisionRestrictedToAmbient_comp_ι
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    excisionRestrictedToAmbient A Z ≫ (excisionAmbientSC A Z).ι =
      (excisionRestrictedSC A Z).ι := by
  rfl

/-- The simplicial map underlying inclusion of restricted cover-small
simplices into ambient cover-small simplices. -/
def restrictedCoverSmallSSetMap {X α : Type} [TopologicalSpace X]
    (A : Set X) (U : α → Set X) :
    (SingularSubdivision.coverSmallSSet (restrictedCover A U) : SSet) ⟶
      (SingularSubdivision.coverSmallSSet U : SSet) := by
  apply (SingularSubdivision.coverSmallSSet U).lift
    ((SingularSubdivision.coverSmallSSet (restrictedCover A U)).ι ≫
      TopCat.toSSet.map (subspaceInclusion A))
  rw [SSet.Subcomplex.range_comp,
    show SSet.Subcomplex.range
        (SingularSubdivision.coverSmallSSet (restrictedCover A U)).ι =
      SingularSubdivision.coverSmallSSet (restrictedCover A U) from
        Subfunctor.range_ι _,
    SingularSubdivision.coverSmallSSet,
    SSet.Subcomplex.image_iSup]
  apply iSup_le
  intro a
  rw [← SSet.Subcomplex.range_comp]
  refine le_iSup_of_le a ?_
  rw [← Functor.map_comp,
    ← restrictedCoverMemberMap_comp A U a, Functor.map_comp,
    SSet.Subcomplex.range_comp]
  exact SSet.Subcomplex.image_le_range _ _

/-- Inclusion of a subspace carries chains subordinate to the restricted
cover into chains subordinate to the ambient cover. -/
noncomputable def restrictedCoverSmallMap {X α : Type} [TopologicalSpace X]
    (A : Set X) (U : α → Set X) :
    SingularSubdivision.coverSmallChains (restrictedCover A U) ⟶
      SingularSubdivision.coverSmallChains U :=
  ssetChains.map (restrictedCoverSmallSSetMap A U)

@[reassoc] theorem restrictedCoverSmallSSetMap_comp_ι
    {X α : Type} [TopologicalSpace X] (A : Set X) (U : α → Set X) :
    restrictedCoverSmallSSetMap A U ≫
        (SingularSubdivision.coverSmallSSet U).ι =
      (SingularSubdivision.coverSmallSSet (restrictedCover A U)).ι ≫
        TopCat.toSSet.map (subspaceInclusion A) := by
  exact SSet.Subcomplex.lift_ι _ _

@[reassoc] theorem excisionAmbientSmallSSetIso_hom_comp_ι
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionAmbientSmallSSetIso A Z).hom ≫
        (SingularSubdivision.coverSmallSSet (excisionCover A Z)).ι =
      (excisionAmbientSC A Z).ι := by
  exact eqToIso_subcomplex_hom_comp_ι _ _
    (excisionCoverSmallSSet_eq_ambientSC A Z).symm

@[reassoc] theorem excisionRestrictedSmallSSetIso_hom_comp_ι
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionRestrictedSmallSSetIso A Z).hom ≫
        (SingularSubdivision.coverSmallSSet
          (restrictedCover A (excisionCover A Z))).ι ≫
        TopCat.toSSet.map (subspaceInclusion A) =
      (excisionRestrictedSC A Z).ι := by
  dsimp [excisionRestrictedSmallSSetIso]
  simp only [Category.assoc]
  change eqToHom _ ≫
    ((asIso (Subfunctor.toRange (restrictedExcisionSSetMap A Z))).inv ≫
      restrictedExcisionSSetMap A Z) = _
  rw [rangeIso_hom_comp]
  apply eqToIso_subcomplex_hom_comp_ι _ _
  symm
  rw [← restrictedExcisionCoverSmallSSet_image_eq_restrictedSC A Z,
    SSet.Subcomplex.image_eq_range]
  rfl

/-- The named subcomplex inclusion square is exactly the simplicial map used
to define the production cover-small comparison. -/
theorem excisionTargetSSet_square
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    excisionRestrictedToAmbient A Z ≫
        (excisionAmbientSmallSSetIso A Z).hom =
      (excisionRestrictedSmallSSetIso A Z).hom ≫
        restrictedCoverSmallSSetMap A (excisionCover A Z) := by
  apply (cancel_mono
    (SingularSubdivision.coverSmallSSet (excisionCover A Z)).ι).1
  rw [Category.assoc, excisionAmbientSmallSSetIso_hom_comp_ι,
    excisionRestrictedToAmbient_comp_ι]
  simp only [Category.assoc]
  slice_rhs 2 3 => rw [restrictedCoverSmallSSetMap_comp_ι]
  exact (excisionRestrictedSmallSSetIso_hom_comp_ι A Z).symm

theorem excisionTargetChain_square
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    ssetChains.map (excisionRestrictedToAmbient A Z) ≫
        (excisionAmbientSmallChainsIso A Z).hom =
      (excisionRestrictedSmallChainsIso A Z).hom ≫
        restrictedCoverSmallMap A (excisionCover A Z) := by
  change ssetChains.map _ ≫ ssetChains.map _ =
    ssetChains.map _ ≫ ssetChains.map _
  rw [← ssetChains.map_comp, ← ssetChains.map_comp]
  congr 1
  exact excisionTargetSSet_square A Z

/-- The target cokernel in the simplicial excision square is canonically the
cover-small relative cokernel used by the homology comparison. -/
noncomputable def excisionTargetSmallRelativeIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    cokernel (ssetChains.map (excisionRestrictedToAmbient A Z)) ≅
      cokernel (restrictedCoverSmallMap A (excisionCover A Z)) :=
  cokernel.mapIso
    (f := ssetChains.map (excisionRestrictedToAmbient A Z))
    (restrictedCoverSmallMap A (excisionCover A Z))
    (excisionRestrictedSmallChainsIso A Z)
    (excisionAmbientSmallChainsIso A Z)
    (excisionTargetChain_square A Z)

/-- Reorder the two subtype predicates in the intersection
`A ∩ Zᶜ ≅ {x : Zᶜ // x ∈ A}`. -/
def excisionIntersectionTopCatIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    TopCat.of (excisedSubspace A Z) ≅ TopCat.of (A ∩ Zᶜ : Set X) where
  hom := TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.2, x.1.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  inv := TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩,
    (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

private def excisionIntersectionToComplement
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionIntersectionSC A Z : SSet) ⟶
      (excisionComplementSC Z : SSet) :=
  SSet.Subcomplex.homOfLE (excisionSubcomplex_bicartSq A Z).le₁₂

private def excisionComplementToAmbient
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionComplementSC Z : SSet) ⟶ (excisionAmbientSC A Z : SSet) :=
  SSet.Subcomplex.homOfLE (excisionSubcomplex_bicartSq A Z).le₂₄

private noncomputable def excisionNamedIsPushout
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    IsPushout
      (SSet.Subcomplex.homOfLE (excisionSubcomplex_bicartSq A Z).le₁₃)
      (excisionIntersectionToComplement A Z)
      (excisionRestrictedToAmbient A Z)
      (excisionComplementToAmbient A Z) := by
  exact (excisionSubcomplex_isPushout A Z).flip

/-- The excision isomorphism on the four named vertices of the bicartesian
square. -/
noncomputable def excisionSmallRelativeIsoOnSquare
    {X : Type} [TopologicalSpace X] (A Z : Set X) :=
  ssetPushoutRelativeIso (excisionNamedIsPushout A Z)

@[reassoc] theorem excisionIntersectionToComplement_comp_ι
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    excisionIntersectionToComplement A Z ≫ (excisionComplementSC Z).ι =
      (excisionIntersectionSC A Z).ι := by
  rfl

@[reassoc] theorem excisionComplementToAmbient_comp_ι
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    excisionComplementToAmbient A Z ≫ (excisionAmbientSC A Z).ι =
      (excisionComplementSC Z).ι := by
  rfl

private def excisionIntersectionRangeSSetIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionIntersectionSC A Z : SSet) ≅
      TopCat.toSSet.obj (TopCat.of (excisedSubspace A Z)) :=
  eqToIso (congrArg
      (fun P : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex ↦ (P : SSet))
      (ambientSubspaceRange_inf A Zᶜ)) ≪≫
    (asIso (Subfunctor.toRange (TopCat.toSSet.map
      (subspaceInclusion (A ∩ Zᶜ : Set X))))).symm ≪≫
    TopCat.toSSet.mapIso (excisionIntersectionTopCatIso A Z).symm

private def excisionComplementRangeSSetIso
    {X : Type} [TopologicalSpace X] (Z : Set X) :
    (excisionComplementSC Z : SSet) ≅
      TopCat.toSSet.obj (TopCat.of (Zᶜ : Set X)) :=
  (asIso (Subfunctor.toRange
    (TopCat.toSSet.map (subspaceInclusion (Zᶜ : Set X))))).symm

noncomputable def excisionComplementRangeChainsIso
    {X : Type} [TopologicalSpace X] (Z : Set X) :
    ssetChains.obj (excisionComplementSC Z : SSet) ≅
      SingularChains (TopCat.of (Zᶜ : Set X)) :=
  ssetChains.mapIso (excisionComplementRangeSSetIso Z)

noncomputable def excisionIntersectionRangeChainsIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    ssetChains.obj (excisionIntersectionSC A Z : SSet) ≅
      SingularChains (TopCat.of (excisedSubspace A Z)) :=
  ssetChains.mapIso (excisionIntersectionRangeSSetIso A Z)

@[reassoc] theorem excisionComplementRangeSSetIso_hom_comp_ι
    {X : Type} [TopologicalSpace X] (Z : Set X) :
    (excisionComplementRangeSSetIso Z).hom ≫
        TopCat.toSSet.map (subspaceInclusion (Zᶜ : Set X)) =
      (excisionComplementSC Z).ι := by
  exact rangeIso_hom_comp _

theorem excisionIntersectionTopCatIso_inv_comp_inclusions
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionIntersectionTopCatIso A Z).inv ≫
        subspaceInclusion (excisedSubspace A Z) ≫
        subspaceInclusion (Zᶜ : Set X) =
      subspaceInclusion (A ∩ Zᶜ : Set X) := by
  ext x
  rfl

@[reassoc] theorem excisionIntersectionRangeSSetIso_hom_comp_ι
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionIntersectionRangeSSetIso A Z).hom ≫
        TopCat.toSSet.map (subspaceInclusion (excisedSubspace A Z)) ≫
        TopCat.toSSet.map (subspaceInclusion (Zᶜ : Set X)) =
      (excisionIntersectionSC A Z).ι := by
  dsimp [excisionIntersectionRangeSSetIso]
  simp only [Category.assoc]
  slice_lhs 3 5 =>
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp,
      excisionIntersectionTopCatIso_inv_comp_inclusions]
  slice_lhs 2 3 => exact rangeIso_hom_comp _
  apply eqToIso_subcomplex_hom_comp_ι _ _
  exact ambientSubspaceRange_inf A Zᶜ

theorem excisionSourceSSet_square
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    excisionIntersectionToComplement A Z ≫
        (excisionComplementRangeSSetIso Z).hom =
      (excisionIntersectionRangeSSetIso A Z).hom ≫
        TopCat.toSSet.map (subspaceInclusion (excisedSubspace A Z)) := by
  apply (cancel_mono
    (TopCat.toSSet.map (subspaceInclusion (Zᶜ : Set X)))).1
  rw [Category.assoc, excisionComplementRangeSSetIso_hom_comp_ι,
    excisionIntersectionToComplement_comp_ι]
  simp only [Category.assoc]
  exact (excisionIntersectionRangeSSetIso_hom_comp_ι A Z).symm

theorem excisionSourceChain_square
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    ssetChains.map (excisionIntersectionToComplement A Z) ≫
        (excisionComplementRangeChainsIso Z).hom =
      (excisionIntersectionRangeChainsIso A Z).hom ≫
        singularSubspaceMap (excisedSubspace A Z) := by
  change ssetChains.map _ ≫ ssetChains.map _ =
    ssetChains.map _ ≫ ssetChains.map _
  rw [← ssetChains.map_comp, ← ssetChains.map_comp]
  congr 1
  exact excisionSourceSSet_square A Z

/-- The source cokernel in the simplicial excision square is the production
relative cokernel of the excised pair. -/
noncomputable def excisionSourceRelativeIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    cokernel (ssetChains.map (excisionIntersectionToComplement A Z)) ≅
      cokernel (singularSubspaceMap (excisedSubspace A Z)) :=
  cokernel.mapIso
    (f := ssetChains.map (excisionIntersectionToComplement A Z))
    (singularSubspaceMap (excisedSubspace A Z))
    (excisionIntersectionRangeChainsIso A Z)
    (excisionComplementRangeChainsIso Z)
    (excisionSourceChain_square A Z)

@[reassoc] theorem restrictedCoverSmallMap_comp_ι
    {X α : Type} [TopologicalSpace X] (A : Set X) (U : α → Set X) :
    restrictedCoverSmallMap A U ≫
        SingularSubdivision.coverSmallChains.ι U =
      SingularSubdivision.coverSmallChains.ι (restrictedCover A U) ≫
        singularSubspaceMap A := by
  change ssetChains.map _ ≫ ssetChains.map _ =
    ssetChains.map _ ≫ ssetChains.map _
  rw [← ssetChains.map_comp, ← ssetChains.map_comp,
    restrictedCoverSmallSSetMap_comp_ι]

noncomputable instance coverSmallChains_ι_mono
    {X α : Type} [TopologicalSpace X] (U : α → Set X) :
    Mono (SingularSubdivision.coverSmallChains.ι U) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦
    SingularSubdivision.coverSmallChains_ι_component_mono U n

noncomputable instance restrictedCoverSmallMap_mono
    {X α : Type} [TopologicalSpace X] (A : Set X) (U : α → Set X) :
    Mono (restrictedCoverSmallMap A U) := by
  haveI : Mono (SingularSubdivision.coverSmallChains.ι
      (restrictedCover A U) ≫ singularSubspaceMap A) := inferInstance
  exact mono_of_mono_fac (restrictedCoverSmallMap_comp_ι A U)

/-- On the excised side the cover-small relative cokernel is canonically the
ordinary production relative cokernel, because both restricted covers contain
the whole relevant space. -/
noncomputable def excisedCoverSmallRelativeIso
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    cokernel (restrictedCoverSmallMap (excisedSubspace A Z)
      (restrictedCover (Zᶜ : Set X) (excisionCover A Z))) ≅
      cokernel (singularSubspaceMap (excisedSubspace A Z)) :=
  cokernel.mapIso (f := restrictedCoverSmallMap (excisedSubspace A Z)
      (restrictedCover (Zᶜ : Set X) (excisionCover A Z)))
    (singularSubspaceMap (excisedSubspace A Z))
    (excisionIntersectionSmallChainsIso A Z)
    (excisionComplementSmallChainsIso A Z) (by
      rw [show (excisionIntersectionSmallChainsIso A Z).hom =
          SingularSubdivision.coverSmallChains.ι
            (restrictedCover (excisedSubspace A Z)
              (restrictedCover (Zᶜ : Set X) (excisionCover A Z))) by
        apply coverSmallChainsIsoOfEqTop_hom,
        show (excisionComplementSmallChainsIso A Z).hom =
          SingularSubdivision.coverSmallChains.ι
            (restrictedCover (Zᶜ : Set X) (excisionCover A Z)) by
        apply coverSmallChainsIsoOfEqTop_hom]
      exact restrictedCoverSmallMap_comp_ι (excisedSubspace A Z)
        (restrictedCover (Zᶜ : Set X) (excisionCover A Z)))

/-- The map from the relative quotient of restricted cover-small chains to
the ordinary relative cokernel of the pair `(X,A)`. -/
noncomputable def coverSmallRelativeMap
    {X α : Type} [TopologicalSpace X] (A : Set X) (U : α → Set X) :
    cokernel (restrictedCoverSmallMap A U) ⟶
      cokernel (singularSubspaceMap A) :=
  cokernel.map (restrictedCoverSmallMap A U) (singularSubspaceMap A)
    (SingularSubdivision.coverSmallChains.ι (restrictedCover A U))
    (SingularSubdivision.coverSmallChains.ι U)
    (restrictedCoverSmallMap_comp_ι A U)

/-- The relative small-chain comparison is a homology isomorphism in degrees
at least two.  This is the exact range needed by positive-degree excision and
the sphere shift. -/
theorem coverSmallRelative_homologyMap_isIso_add_two
    {X α : Type} [TopologicalSpace X] (A : Set X) (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a)
    (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (coverSmallRelativeMap A U) (n + 2)) := by
  apply cokernelSquare_homologyMap_isIso
    (restrictedCoverSmallMap A U) (singularSubspaceMap A)
    (SingularSubdivision.coverSmallChains.ι (restrictedCover A U))
    (SingularSubdivision.coverSmallChains.ι U)
    (restrictedCoverSmallMap_comp_ι A U) (n + 2)
  · simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      SingularSubdivision.coverSmall_homologyMap_isIso_succ
        (restrictedCover A U) (restrictedCover_isOpen A U hUOpen)
        (by rw [restrictedCover_iUnion_eq_univ A U
          (Set.Subset.antisymm (by simp) hUCover)]) (n + 1)
  · simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      SingularSubdivision.coverSmall_homologyMap_isIso_succ
        U hUOpen hUCover (n + 1)
  · intro j hj
    have hj' : j = n + 1 := by simpa using hj
    subst j
    simpa using SingularSubdivision.coverSmall_homologyMap_isIso_succ
      (restrictedCover A U) (restrictedCover_isOpen A U hUOpen)
      (by rw [restrictedCover_iUnion_eq_univ A U
        (Set.Subset.antisymm (by simp) hUCover)]) n
  · intro j hj
    have hj' : j = n + 1 := by simpa using hj
    subst j
    simpa using SingularSubdivision.coverSmall_homologyMap_isIso_succ
      U hUOpen hUCover n

/-- The relative small-chain comparison is also an isomorphism in degree one.
The adjacent degree required by the exact-sequence argument is precisely the
zeroth small-chain comparison. -/
theorem coverSmallRelative_homologyMap_isIso_one
    {X α : Type} [TopologicalSpace X] (A : Set X) (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a) :
    IsIso (HomologicalComplex.homologyMap
      (coverSmallRelativeMap A U) 1) := by
  have hRestrictedCover : Set.univ ⊆ ⋃ a, restrictedCover A U a := by
    rw [restrictedCover_iUnion_eq_univ A U
      (Set.Subset.antisymm (by simp) hUCover)]
  apply cokernelSquare_homologyMap_isIso
    (restrictedCoverSmallMap A U) (singularSubspaceMap A)
    (SingularSubdivision.coverSmallChains.ι (restrictedCover A U))
    (SingularSubdivision.coverSmallChains.ι U)
    (restrictedCoverSmallMap_comp_ι A U) 1
  · simpa using SingularSubdivision.coverSmall_homologyMap_isIso_succ
      (restrictedCover A U) (restrictedCover_isOpen A U hUOpen)
      hRestrictedCover 0
  · simpa using SingularSubdivision.coverSmall_homologyMap_isIso_succ
      U hUOpen hUCover 0
  · intro j hj
    have hj' : j = 0 := by simpa using hj
    subst j
    exact SingularSubdivision.coverSmall_homologyMap_isIso_zero
      (restrictedCover A U) (restrictedCover_isOpen A U hUOpen)
      hRestrictedCover
  · intro j hj
    have hj' : j = 0 := by simpa using hj
    subst j
    exact SingularSubdivision.coverSmall_homologyMap_isIso_zero
      U hUOpen hUCover

/-- Subdivision proves that chains subordinate to the standard excision cover
compute the positive-degree singular homology of `X`.  This is the geometric
half of open-cover excision; the other half is the quotient comparison of
pairs. -/
noncomputable instance excisionCover_homologyMap_isIso_succ
    {X : Type} [TopologicalSpace X] (A Z : Set X)
    (hZclosed : IsClosed Z) (hZ : Z ⊆ interior A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (SingularSubdivision.coverSmallChains.ι (excisionCover A Z)) (n + 1)) :=
  SingularSubdivision.coverSmall_homologyMap_isIso_succ (excisionCover A Z)
    (excisionCover_isOpen A Z hZclosed)
    (by rw [excisionCover_iUnion_eq_univ A Z hZ]) n

/-- The restriction of a continuous map to subspaces which it carries into
one another. -/
def subspaceMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
  TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x, hf x.2⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[reassoc] theorem subspaceMap_inclusion
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    subspaceMap A B f hf ≫ subspaceInclusion B =
      subspaceInclusion A ≫ TopCat.ofHom f := by
  ext x
  rfl

/-- The natural square of absolute and subspace singular-chain maps. -/
theorem singularSubspaceMap_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    singularSubspaceMap A ≫
        ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f) =
      ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (subspaceMap A B f hf) ≫
        singularSubspaceMap B := by
  dsimp only [singularSubspaceMap]
  rw [← Functor.map_comp, ← Functor.map_comp, subspaceMap_inclusion]

private noncomputable def absoluteMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    SingularChains (TopCat.of X) ⟶ SingularChains (TopCat.of Y) :=
  ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)

/-- The induced map between the direct cokernel presentations. -/
noncomputable def relativeCokernelMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    cokernel (singularSubspaceMap A) ⟶ cokernel (singularSubspaceMap B) :=
  cokernel.desc (singularSubspaceMap A)
    (absoluteMap f ≫ cokernel.π (singularSubspaceMap B)) (by
      dsimp only [absoluteMap]
      slice_lhs 1 2 => rw [singularSubspaceMap_naturality A B f hf]
      rw [Category.assoc, cokernel.condition, comp_zero])

/-- The direct relative map is the canonical cokernel map of the natural
square on subspace and ambient singular chains.  This form is what the
five-lemma comparison consumes. -/
theorem relativeCokernelMap_eq_cokernel_map
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    relativeCokernelMap A B f hf =
      cokernel.map (singularSubspaceMap A) (singularSubspaceMap B)
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (subspaceMap A B f hf))
        (absoluteMap f) (singularSubspaceMap_naturality A B f hf) := by
  apply (cancel_epi (cokernel.π (singularSubspaceMap A))).1
  dsimp [relativeCokernelMap]

/-- A continuous map of pairs induces a map of relative singular-chain
complexes.  The definition uses the direct cokernel presentation and the
proved comparison with `RelativeSingularChains`. -/
noncomputable def relativeSingularMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    RelativeSingularChains A ⟶ RelativeSingularChains B :=
  (relativeSingularChainsIsoCokernelSubspaceMap A).hom ≫
    relativeCokernelMap A B f hf ≫
    (relativeSingularChainsIsoCokernelSubspaceMap B).inv

/-- Consumer-level comparison for a map of pairs.  If its maps on the
subspace and ambient absolute singular homology are isomorphisms in degree
`i` and the preceding degree, then its map on relative singular homology is
an isomorphism in degree `i`.

This is the reusable collar/deformation interface: geometric arguments only
need to establish ordinary homotopy equivalences on the two vertical spaces;
the relative conclusion is supplied here by the long exact sequence. -/
theorem relativeSingularMap_homologyMap_isIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B)
    (i : ℕ)
    (hsub : IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (subspaceMap A B f hf)) i))
    (hamb : IsIso (HomologicalComplex.homologyMap (absoluteMap f) i))
    (hsubPrev : ∀ j, (ComplexShape.down ℕ).Rel i j →
      IsIso (HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (subspaceMap A B f hf)) j))
    (hambPrev : ∀ j, (ComplexShape.down ℕ).Rel i j →
      IsIso (HomologicalComplex.homologyMap (absoluteMap f) j)) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap A B f hf) i) := by
  let a := ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (subspaceMap A B f hf)
  let b := absoluteMap f
  have hcok : IsIso (HomologicalComplex.homologyMap
      (cokernel.map (singularSubspaceMap A) (singularSubspaceMap B) a b
        (singularSubspaceMap_naturality A B f hf)) i) :=
    cokernelSquare_homologyMap_isIso
      (singularSubspaceMap A) (singularSubspaceMap B) a b
      (singularSubspaceMap_naturality A B f hf) i
      hsub hamb hsubPrev hambPrev
  letI := hcok
  dsimp [relativeSingularMap]
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp,
    relativeCokernelMap_eq_cokernel_map]
  infer_instance

theorem relativeProjection_comp_cokernelIso_hom
    {X : Type} [TopologicalSpace X] (A : Set X) :
    relativeSingularProjection A ≫
        (relativeSingularChainsIsoCokernelSubspaceMap A).hom =
      cokernel.π (singularSubspaceMap A) := by
  dsimp [relativeSingularProjection,
    relativeSingularChainsIsoCokernelSubspaceMap]
  apply cokernel.π_desc

/-- Naturality of the absolute-to-relative projection for a map of pairs. -/
theorem relativeSingularMap_projection_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    absoluteMap f ≫ relativeSingularProjection B =
      relativeSingularProjection A ≫ relativeSingularMap A B f hf := by
  apply (cancel_mono
    (relativeSingularChainsIsoCokernelSubspaceMap B).hom).1
  rw [Category.assoc, relativeProjection_comp_cokernelIso_hom]
  simp only [relativeSingularMap, Category.assoc]
  slice_rhs 1 2 => rw [relativeProjection_comp_cokernelIso_hom]
  dsimp only [relativeCokernelMap]
  rw [cokernel.π_desc]
  simp

/-- The induced map on relative singular homology. -/
noncomputable def relativeSingularHomologyMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B)
    (n : ℕ) :
    (RelativeSingularChains A).homology n ⟶
      (RelativeSingularChains B).homology n :=
  HomologicalComplex.homologyMap (relativeSingularMap A B f hf) n

/-! ## The production excision map -/

/-- Inclusion of the complement of the excised set. -/
def excisionInclusion {X : Type} [TopologicalSpace X] (Z : Set X) :
    C((Zᶜ : Set X), X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem excisionInclusion_mapsTo {X : Type} [TopologicalSpace X]
    (A Z : Set X) :
    Set.MapsTo (excisionInclusion Z) (excisedSubspace A Z) A := by
  intro x hx
  exact hx

/-- The production relative-chain map appearing in excision. -/
noncomputable def relativeExcisionMap {X : Type} [TopologicalSpace X]
    (A Z : Set X) :
    RelativeSingularChains (excisedSubspace A Z) ⟶
      RelativeSingularChains A :=
  relativeSingularMap (excisedSubspace A Z) A (excisionInclusion Z)
    (excisionInclusion_mapsTo A Z)

theorem excisionComplement_to_productionSSet
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionComplementRangeSSetIso Z).inv ≫
        excisionComplementToAmbient A Z ≫
        (excisionAmbientSmallSSetIso A Z).hom ≫
        (SingularSubdivision.coverSmallSSet (excisionCover A Z)).ι =
      TopCat.toSSet.map (TopCat.ofHom (excisionInclusion Z)) := by
  slice_lhs 3 4 => rw [excisionAmbientSmallSSetIso_hom_comp_ι]
  slice_lhs 2 3 => rw [excisionComplementToAmbient_comp_ι]
  dsimp [excisionComplementRangeSSetIso]
  change Subfunctor.toRange (TopCat.toSSet.map
      (subspaceInclusion (Zᶜ : Set X))) ≫
      (SSet.Subcomplex.range (TopCat.toSSet.map
        (subspaceInclusion (Zᶜ : Set X)))).ι = _
  rw [Subfunctor.toRange_ι]
  rfl

theorem excisionComplement_to_productionChains
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    (excisionComplementRangeChainsIso Z).inv ≫
        ssetChains.map (excisionComplementToAmbient A Z) ≫
        (excisionAmbientSmallChainsIso A Z).hom ≫
        SingularSubdivision.coverSmallChains.ι (excisionCover A Z) =
      absoluteMap (excisionInclusion Z) := by
  change ssetChains.map _ ≫ ssetChains.map _ ≫ ssetChains.map _ ≫
    ssetChains.map _ = ssetChains.map _
  rw [← ssetChains.map_comp, ← ssetChains.map_comp,
    ← ssetChains.map_comp]
  congr 1
  exact excisionComplement_to_productionSSet A Z

/-- The excision comparison assembled through the simplicial pushout and the
cover-small relative complex, in the direct cokernel presentation. -/
noncomputable def excisionCokernelComposite
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    cokernel (singularSubspaceMap (excisedSubspace A Z)) ⟶
      cokernel (singularSubspaceMap A) :=
  (excisionSourceRelativeIso A Z).inv ≫
    (excisionSmallRelativeIsoOnSquare A Z).hom ≫
    (excisionTargetSmallRelativeIso A Z).hom ≫
    coverSmallRelativeMap A (excisionCover A Z)

theorem excisionCokernelComposite_eq_relativeCokernelMap
    {X : Type} [TopologicalSpace X] (A Z : Set X) :
    excisionCokernelComposite A Z =
      relativeCokernelMap (excisedSubspace A Z) A (excisionInclusion Z)
        (excisionInclusion_mapsTo A Z) := by
  apply (cancel_epi (cokernel.π (singularSubspaceMap
    (excisedSubspace A Z)))).1
  simp [excisionCokernelComposite, excisionSourceRelativeIso,
    excisionSmallRelativeIsoOnSquare, ssetPushoutRelativeIso,
    ssetPushoutRelativeMap, excisionTargetSmallRelativeIso,
    coverSmallRelativeMap, relativeCokernelMap]
  slice_lhs 1 4 => exact excisionComplement_to_productionChains A Z

theorem excisionCokernelComposite_homologyMap_isIso_add_two
    {X : Type} [TopologicalSpace X] (A Z : Set X)
    (hZclosed : IsClosed Z) (hZ : Z ⊆ interior A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (excisionCokernelComposite A Z) (n + 2)) := by
  have hCover : Set.univ ⊆ ⋃ b, excisionCover A Z b := by
    rw [excisionCover_iUnion_eq_univ A Z hZ]
  letI := coverSmallRelative_homologyMap_isIso_add_two A
    (excisionCover A Z) (excisionCover_isOpen A Z hZclosed) hCover n
  dsimp [excisionCokernelComposite]
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  infer_instance

theorem excisionCokernelComposite_homologyMap_isIso_one
    {X : Type} [TopologicalSpace X] (A Z : Set X)
    (hZclosed : IsClosed Z) (hZ : Z ⊆ interior A) :
    IsIso (HomologicalComplex.homologyMap
      (excisionCokernelComposite A Z) 1) := by
  have hCover : Set.univ ⊆ ⋃ b, excisionCover A Z b := by
    rw [excisionCover_iUnion_eq_univ A Z hZ]
  letI := coverSmallRelative_homologyMap_isIso_one A
    (excisionCover A Z) (excisionCover_isOpen A Z hZclosed) hCover
  dsimp [excisionCokernelComposite]
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  infer_instance

theorem relativeCokernelExcision_homologyMap_isIso_add_two
    {X : Type} [TopologicalSpace X] (A Z : Set X)
    (hZclosed : IsClosed Z) (hZ : Z ⊆ interior A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeCokernelMap (excisedSubspace A Z) A (excisionInclusion Z)
        (excisionInclusion_mapsTo A Z)) (n + 2)) := by
  rw [← excisionCokernelComposite_eq_relativeCokernelMap A Z]
  exact excisionCokernelComposite_homologyMap_isIso_add_two
    A Z hZclosed hZ n

theorem relativeCokernelExcision_homologyMap_isIso_one
    {X : Type} [TopologicalSpace X] (A Z : Set X)
    (hZclosed : IsClosed Z) (hZ : Z ⊆ interior A) :
    IsIso (HomologicalComplex.homologyMap
      (relativeCokernelMap (excisedSubspace A Z) A (excisionInclusion Z)
        (excisionInclusion_mapsTo A Z)) 1) := by
  rw [← excisionCokernelComposite_eq_relativeCokernelMap A Z]
  exact excisionCokernelComposite_homologyMap_isIso_one
    A Z hZclosed hZ

/-- Production open-cover excision in positive relative degrees. -/
theorem relativeExcisionMap_homologyMap_isIso_add_two
    {X : Type} [TopologicalSpace X] (A Z : Set X)
    (hZclosed : IsClosed Z) (hZ : Z ⊆ interior A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeExcisionMap A Z) (n + 2)) := by
  letI := relativeCokernelExcision_homologyMap_isIso_add_two
    A Z hZclosed hZ n
  dsimp [relativeExcisionMap, relativeSingularMap]
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  infer_instance

/-- Production open-cover excision in degree one. -/
theorem relativeExcisionMap_homologyMap_isIso_one
    {X : Type} [TopologicalSpace X] (A Z : Set X)
    (hZclosed : IsClosed Z) (hZ : Z ⊆ interior A) :
    IsIso (HomologicalComplex.homologyMap
      (relativeExcisionMap A Z) 1) := by
  letI := relativeCokernelExcision_homologyMap_isIso_one
    A Z hZclosed hZ
  dsimp [relativeExcisionMap, relativeSingularMap]
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  infer_instance

/-- Production open-cover excision in every positive degree. -/
theorem relativeExcisionMap_homologyMap_isIso_succ
    {X : Type} [TopologicalSpace X] (A Z : Set X)
    (hZclosed : IsClosed Z) (hZ : Z ⊆ interior A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeExcisionMap A Z) (n + 1)) := by
  cases n with
  | zero => exact relativeExcisionMap_homologyMap_isIso_one A Z hZclosed hZ
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        relativeExcisionMap_homologyMap_isIso_add_two A Z hZclosed hZ n

/-- Open-cover excision, in the exact positive-degree range consumed by the
sphere shift. -/
def RelativeExcisionStatement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (A Z : Set X), IsClosed Z →
    Z ⊆ interior A → ∀ n : ℕ,
      IsIso (HomologicalComplex.homologyMap
        (relativeExcisionMap A Z) (n + 2))

theorem relativeExcision : RelativeExcisionStatement := by
  intro X _ A Z hZclosed hZ n
  exact relativeExcisionMap_homologyMap_isIso_add_two
    A Z hZclosed hZ n

#print axioms subspaceMap_inclusion
#print axioms singularSubspaceMap_naturality
#print axioms relativeSingularMap
#print axioms relativeCokernelMap_eq_cokernel_map
#print axioms relativeSingularMap_homologyMap_isIso
#print axioms relativeSingularMap_projection_naturality
#print axioms relativeSingularHomologyMap
#print axioms relativeExcisionMap
#print axioms subcomplexMayerVietorisShortComplex_shortExact
#print axioms subcomplexMayerVietorisConnecting
#print axioms subcomplexMayerVietoris_exact_intersection
#print axioms subcomplexMayerVietoris_exact_pieces
#print axioms subcomplexMayerVietoris_exact_union
#print axioms subcomplexChains_isPushout
#print axioms ambientSubspaceRangeInclusion_square
#print axioms ambientSubspaceRangeChainsIso_naturality
#print axioms ambientSubspaceRangeHomologyIso_naturality
#print axioms ambientIntersectionRangeToLeft_naturality
#print axioms ambientIntersectionRangeToRight_naturality
#print axioms ambientLeftRangeToUnion_naturality
#print axioms ambientRightRangeToUnion_naturality
#print axioms coverMemberRangeInclusion_square
#print axioms coverMemberRangeChainsIso_naturality
#print axioms coverMemberRangeHomologyIso_naturality
#print axioms subcomplexUnionRelativeIso
#print axioms cokernelSquare_homologyMap_isIso
#print axioms restrictedCoverSmallMap_comp_ι
#print axioms coverSmallRelative_homologyMap_isIso_add_two
#print axioms coverSmallRelative_homologyMap_isIso_one
#print axioms ssetPushoutRelativeIso
#print axioms excisionSubcomplex_bicartSq
#print axioms excisionSmallRelativeIso
#print axioms excisedCoverSmallRelativeIso
#print axioms excisionAmbientSmallChainsIso
#print axioms excisionRestrictedSmallChainsIso
#print axioms excisionCokernelComposite_eq_relativeCokernelMap
#print axioms relativeExcisionMap_homologyMap_isIso_add_two
#print axioms relativeExcisionMap_homologyMap_isIso_one
#print axioms relativeExcisionMap_homologyMap_isIso_succ
#print axioms relativeExcision

end ConstructionTargets.SingularExcision
