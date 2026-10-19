import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.CircleSingularHomology
import ConstructionTargets.Surfaces
import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.PolygonCellPiOne
import ConstructionTargets.IntegralOpenCoverMayerVietoris

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t01a03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01a03_I2 := 𝓘(ℝ, apm_t01a03_E2)
abbrev apm_t01a03_Torus := Circle × Circle
abbrev apm_t01a03_TwoCircles := Sum Circle Circle

inductive apm_t01a03_wedgeRel :
    Sum Circle Circle → Sum Circle Circle → Prop
  | base : apm_t01a03_wedgeRel (.inl 1) (.inr 1)

def apm_t01a03_Wedge :=
  Quotient (Relation.EqvGen.setoid apm_t01a03_wedgeRel)

noncomputable instance : TopologicalSpace apm_t01a03_Wedge :=
  TopologicalSpace.coinduced
    (fun x : Sum Circle Circle =>
      Quotient.mk (Relation.EqvGen.setoid apm_t01a03_wedgeRel) x)
    inferInstance

def apm_t01a03_wedgeBase : apm_t01a03_Wedge :=
  Quotient.mk _ (.inl 1)

abbrev apm_t01a03_H1 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t01a03_H1map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

def apm_t01a03_hasGenusTwo (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of S)) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01a03_H1 S ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
    Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of S)) ≅ ModuleCat.of ℤ ℤ)

def apm_t01a03_HasRetraction {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (i : C(A, X)) : Prop :=
  ∃ r : C(X, A), ∀ a, r (i a) = a

abbrev apm_t01a03_PuncturedTorus :=
  {x : apm_t01a03_Torus // x ≠ ((1 : Circle), (1 : Circle))}

abbrev apm_t01a03_OpenDisk := Metric.ball (0 : ℂ) 1

abbrev apm_t01a03_Sphere2 :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def apm_t01a03_IsMiddleCircle {S : Type} [TopologicalSpace S]
    (middle : C(Circle, S)) : Prop :=
  Topology.IsEmbedding middle ∧
    Nonempty ({x : S // x ∉ Set.range middle} ≃ₜ
      Sum apm_t01a03_PuncturedTorus apm_t01a03_PuncturedTorus)

def apm_t01a03_IsTypicalWedge
    (wedge : C(apm_t01a03_Wedge, apm_t01a03_Torus)) : Prop :=
  Topology.IsEmbedding wedge ∧
    Nonempty ({x : apm_t01a03_Torus // x ∉ Set.range wedge} ≃ₜ
      apm_t01a03_OpenDisk)

def apm_t01a03_IsSeparatingTwoCircles {S : Type} [TopologicalSpace S]
    (circles : C(apm_t01a03_TwoCircles, S)) : Prop :=
  Topology.IsEmbedding circles ∧
    ∃ punctures : Fin 4 → apm_t01a03_Sphere2,
      Function.Injective punctures ∧
      Nonempty ({x : S // x ∉ Set.range circles} ≃ₜ
        {x : apm_t01a03_Sphere2 // x ∉ Set.range punctures})

/-! ## Already-proved functorial obstruction lemmas -/

lemma apm_t01a03_noRetraction_twoCircles
    {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (i : C(apm_t01a03_TwoCircles, S)) :
    ¬apm_t01a03_HasRetraction i := by
  rintro ⟨r, hr⟩
  have hr_surj : Function.Surjective r := fun a ↦ ⟨i a, hr a⟩
  letI : ConnectedSpace apm_t01a03_TwoCircles :=
    hr_surj.connectedSpace r.continuous
  have hclopen :=
    (connectedSpace_iff_clopen.mp
      (inferInstance : ConnectedSpace apm_t01a03_TwoCircles)).2
      (Set.range (Sum.inl : Circle → apm_t01a03_TwoCircles)) isClopen_range_inl
  rcases hclopen with hempty | huniv
  · exact (Set.range_nonempty
      (Sum.inl : Circle → apm_t01a03_TwoCircles)).ne_empty hempty
  · have hmem : (Sum.inr (1 : Circle) : apm_t01a03_TwoCircles) ∈
        Set.range (Sum.inl : Circle → apm_t01a03_TwoCircles) := by
      rw [huniv]
      trivial
    rcases hmem with ⟨z, hz⟩
    exact Sum.inl_ne_inr hz

lemma apm_t01a03_fundamentalGroupMap_injective_of_retraction
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a : A) (h : apm_t01a03_HasRetraction i) :
    Function.Injective (FundamentalGroup.map i a) := by
  rcases h with ⟨r, hr⟩
  intro p q hpq
  have hcomp : r.comp i = ContinuousMap.id A := by
    ext x
    exact hr x
  change (FundamentalGroupoid.map i).map p =
    (FundamentalGroupoid.map i).map q at hpq
  have hpq' := congrArg (fun z ↦ (FundamentalGroupoid.map r).map z) hpq
  change ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map p) =
    ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map q) at hpq'
  have hfun : FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r =
      CategoryTheory.Functor.id (FundamentalGroupoid A) := by
    rw [← FundamentalGroupoid.map_comp, hcomp, FundamentalGroupoid.map_id]
  rw [hfun] at hpq'
  exact hpq'

lemma apm_t01a03_H1map_injective_of_retraction
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (h : apm_t01a03_HasRetraction i) :
    Function.Injective (apm_t01a03_H1map i) := by
  rcases h with ⟨r, hr⟩
  have hcomp : r.comp i = ContinuousMap.id A := by
    ext x
    exact hr x
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hfun : apm_t01a03_H1map i ≫ apm_t01a03_H1map r =
      𝟙 (apm_t01a03_H1 A) := by
    change F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom r) = 𝟙 _
    rw [← F.map_comp]
    change F.map (TopCat.ofHom (r.comp i)) = 𝟙 _
    rw [hcomp]
    exact F.map_id (TopCat.of A)
  intro x y hxy
  have hxy' := congrArg (fun z ↦ apm_t01a03_H1map r z) hxy
  have hx := congrArg (fun q : apm_t01a03_H1 A ⟶ apm_t01a03_H1 A ↦ q x) hfun
  have hy := congrArg (fun q : apm_t01a03_H1 A ⟶ apm_t01a03_H1 A ↦ q y) hfun
  simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using
    hx.symm.trans (hxy'.trans hy)

lemma apm_t01a03_noRetraction_of_H1map_zero
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (hi : apm_t01a03_H1map i = 0)
    (hnonzero : ∃ x : apm_t01a03_H1 A, x ≠ 0) :
    ¬apm_t01a03_HasRetraction i := by
  intro hret
  obtain ⟨x, hx⟩ := hnonzero
  have hinj := apm_t01a03_H1map_injective_of_retraction i hret
  apply hx
  apply hinj
  rw [hi]
  simp

lemma apm_t01a03_noRetraction_circle_of_H1_nontrivial
    [Nontrivial (apm_t01a03_H1 Circle)]
    {X : Type} [TopologicalSpace X] (i : C(Circle, X))
    (hi : apm_t01a03_H1map i = 0) :
    ¬apm_t01a03_HasRetraction i := by
  apply apm_t01a03_noRetraction_of_H1map_zero i hi
  obtain ⟨x, hx⟩ := exists_ne (0 : apm_t01a03_H1 Circle)
  exact ⟨x, hx⟩

/-! ## Independent blueprint obligations -/

/-- The problem's quotient model is the banked finite wedge of two circles,
with the displayed basepoints matched. -/
lemma apm_t01a03_wedge_homeomorph_finiteWedge_two :
    ∃ h : apm_t01a03_Wedge ≃ₜ
        ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin 2),
      h apm_t01a03_wedgeBase =
        ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin 2) 1 := by
  let f : Sum Circle Circle → Fin 2 × Circle
    | .inl z => (0, z)
    | .inr z => (1, z)
  let g : Fin 2 × Circle → Sum Circle Circle := fun p =>
    if p.1 = (0 : Fin 2) then .inl p.2 else .inr p.2
  have hfg : ∀ x, g (f x) = x := by
    rintro (z | z)
    · rfl
    · simp [f, g]
  have hgf : ∀ x, f (g x) = x := by
    rintro ⟨i, z⟩
    fin_cases i <;> simp [f, g]
  have hf_rel {x y : Sum Circle Circle}
      (h : Relation.EqvGen apm_t01a03_wedgeRel x y) :
      Relation.EqvGen
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel
          (Fin 2)) (f x) (f y) := by
    induction h with
    | rel x y h =>
        cases h
        exact Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  have hg_rel {x y : Fin 2 × Circle}
      (h : Relation.EqvGen
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel
          (Fin 2)) x y) :
      Relation.EqvGen apm_t01a03_wedgeRel (g x) (g y) := by
    induction h with
    | rel x y h =>
        rcases h with rfl | ⟨hx, hy⟩
        · exact Relation.EqvGen.refl _
        · rcases x with ⟨i, x⟩
          rcases y with ⟨j, y⟩
          have hx' : x = (1 : Circle) := Subtype.ext hx
          have hy' : y = (1 : Circle) := Subtype.ext hy
          subst x
          subst y
          fin_cases i <;> fin_cases j
          · exact Relation.EqvGen.refl _
          · exact Relation.EqvGen.rel _ _ apm_t01a03_wedgeRel.base
          · exact (Relation.EqvGen.rel _ _ apm_t01a03_wedgeRel.base).symm
          · exact Relation.EqvGen.refl _
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  let F : apm_t01a03_Wedge →
      ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin 2) :=
    Quotient.lift (fun x => Quotient.mk _ (f x))
      (fun _ _ h => Quotient.sound (hf_rel h))
  let G : ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin 2) →
      apm_t01a03_Wedge :=
    Quotient.lift (fun x => Quotient.mk _ (g x))
      (fun _ _ h => Quotient.sound (hg_rel h))
  have hF_cont : Continuous F := by
    apply Continuous.quotient_lift
    apply continuous_coinduced_rng.comp
    apply continuous_sum_dom.mpr
    exact ⟨continuous_const.prodMk continuous_id,
      continuous_const.prodMk continuous_id⟩
  have hG_cont : Continuous G := by
    apply Continuous.quotient_lift
    apply continuous_coinduced_rng.comp
    change Continuous g
    apply Continuous.if
    · intro x hx
      have hc : IsClopen {p : Fin 2 × Circle | p.1 = 0} :=
        (isClopen_discrete {0}).preimage continuous_fst
      rw [hc.frontier_eq] at hx
      simp at hx
    · exact continuous_inl.comp continuous_snd
    · exact continuous_inr.comp continuous_snd
  let h : apm_t01a03_Wedge ≃ₜ
      ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin 2) :=
    { toFun := F
      invFun := G
      left_inv := by rintro ⟨x⟩; exact congrArg (Quotient.mk _) (hfg x)
      right_inv := by rintro ⟨x⟩; exact congrArg (Quotient.mk _) (hgf x)
      continuous_toFun := hF_cont
      continuous_invFun := hG_cont }
  refine ⟨h, ?_⟩
  rfl

/-- The two canonical generators of the free group on two letters do not
commute. -/
lemma apm_t01a03_freeGroup_finTwo_noncommutative :
    ∃ a b : FreeGroup (Fin 2), a * b ≠ b * a :=
  ⟨FreeGroup.of 0, FreeGroup.of 1, by decide⟩

/-- **LIBRARY assembly (point-wedge van Kampen).** The concrete wedge has two
noncommuting based loop classes. -/
theorem apm_t01a03_circleWedge_pi1_noncommutative :
    ∃ a b : FundamentalGroup apm_t01a03_Wedge apm_t01a03_wedgeBase,
      a * b ≠ b * a := by
  obtain ⟨h, hbase⟩ := apm_t01a03_wedge_homeomorph_finiteWedge_two
  obtain ⟨e, _he⟩ := finiteWedge_finSucc_fundamentalGroup_free 1
  obtain ⟨a, b, hab⟩ := apm_t01a03_freeGroup_finTwo_noncommutative
  let hπ :=
    ConstructionTargets.PolygonSurfaceHomology.fundamentalGroupEquivOfHomeomorphEq
      h apm_t01a03_wedgeBase
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin 2) 1) hbase
  let E := hπ.trans e
  refine ⟨E.symm a, E.symm b, ?_⟩
  intro hcomm
  apply hab
  simpa using congrArg E hcomm

/-- The torus target has abelian fundamental group, so any map from a wedge
with two noncommuting loops is noninjective. The source fact is an explicit
hypothesis so this lemma is independently assignable. -/
lemma apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective_aux_circle_comm
    (x : Circle) (p q : FundamentalGroup Circle x) : p * q = q * p := by
  let e := (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x (1 : Circle)).trans
    ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

lemma apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective_aux_torus_comm
    (x : apm_t01a03_Torus) (p q : FundamentalGroup apm_t01a03_Torus x) :
    p * q = q * p := by
  apply (ConstructionTargets.FundamentalGroupProduct.fundamentalGroupProdMulEquiv
    x.1 x.2).injective
  simp only [map_mul, Prod.mul_def, Prod.ext_iff]
  exact ⟨
    apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective_aux_circle_comm _ _ _,
    apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective_aux_circle_comm _ _ _⟩

theorem apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective
    (hsource : ∃ a b : FundamentalGroup apm_t01a03_Wedge apm_t01a03_wedgeBase,
      a * b ≠ b * a)
    (wedge : C(apm_t01a03_Wedge, apm_t01a03_Torus))
    (_hwedge : apm_t01a03_IsTypicalWedge wedge) :
    ¬Function.Injective
      (FundamentalGroup.map wedge apm_t01a03_wedgeBase) := by
  rintro hinj
  obtain ⟨a, b, hab⟩ := hsource
  apply hab
  apply hinj
  rw [map_mul, map_mul]
  exact
    apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective_aux_torus_comm _ _ _

/-! ### Separating circle, without a collar

Collapse the circle to the point at infinity of the one-point
compactification of its complement. The complement is two punctured tori, so
the target is (a copy of) a wedge of two tori, whose `H₁` is `ℤ⁴` and is
reached from the complement. Hence the collapse map is surjective on `H₁`
between two copies of `ℤ⁴`, so it is injective, and it kills the circle
because it sends the circle to one point. No collar or Schoenflies step is
needed. -/

abbrev apm_t01a03_TwoPuncturedTori :=
  Sum apm_t01a03_PuncturedTorus apm_t01a03_PuncturedTorus

/-- Collapsing the circle: `S → OnePoint Y` is continuous, sends the circle to
`∞`, and is the complement homeomorphism off the circle. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_collapse
    {S Y : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Y]
    (middle : C(Circle, S))
    (e : {x : S // x ∉ Set.range middle} ≃ₜ Y) :
    ∃ ρ : C(S, OnePoint Y), (∀ z, ρ (middle z) = OnePoint.infty) ∧
      ∀ x : {x : S // x ∉ Set.range middle}, ρ x = ((e x : Y) : OnePoint Y) := by
  classical
  let A : Set S := Set.range middle
  have hAcompact : IsCompact A := by
    exact isCompact_range middle.continuous
  have hAclosed : IsClosed A := hAcompact.isClosed
  let f : S → OnePoint Y := fun x ↦
    if hx : x ∈ A then OnePoint.infty else ((e ⟨x, hx⟩ : Y) : OnePoint Y)
  have hf : Continuous f := by
    rw [continuous_def]
    intro V hV
    by_cases hinf : OnePoint.infty ∈ V
    · let K : Set Y := (((↑) : Y → OnePoint Y) ⁻¹' V)ᶜ
      have hKcompact : IsCompact K :=
        (OnePoint.isOpen_iff_of_mem hinf).mp hV |>.2
      let g : Y → S := fun y ↦ (e.symm y).1
      have hg : Continuous g := continuous_subtype_val.comp e.symm.continuous
      have hclosed : IsClosed (g '' K) :=
        (hKcompact.image hg).isClosed
      rw [← isClosed_compl_iff]
      convert hclosed using 1
      ext x
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        have hxA : x ∉ A := by
          intro hxA
          apply hx
          simp [f, hxA, hinf]
        refine ⟨e ⟨x, hxA⟩, ?_, ?_⟩
        · simpa [K, f, hxA] using hx
        · simp [g]
      · rintro ⟨y, hy, rfl⟩
        have hnotA : g y ∉ A := (e.symm y).2
        simpa [f, g, hnotA, K] using hy
    · have hpreopen : IsOpen (((↑) : Y → OnePoint Y) ⁻¹' V) :=
        (OnePoint.isOpen_iff_of_notMem hinf).mp hV
      have hsubopen : IsOpen (e ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' V)) :=
        hpreopen.preimage e.continuous
      have hopen_image : IsOpen
          (((↑) : {x : S // x ∉ A} → S) ''
            (e ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' V))) := by
        exact hAclosed.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap _ hsubopen
      convert hopen_image using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        have hxA : x ∉ A := by
          intro hxA
          have : f x = OnePoint.infty := by simp [f, hxA]
          exact hinf (this ▸ hx)
        refine ⟨⟨x, hxA⟩, ?_, rfl⟩
        simpa [f, hxA] using hx
      · rintro ⟨x, hx, rfl⟩
        simpa [f, x.2] using hx
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro z
    simp [f, A]
  · intro x
    have hxA : x.1 ∉ A := by simpa [A] using x.2
    simp [f, hxA]

/-- A constant map induces zero on `H₁`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_const
    {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (f : C(X, Z)) (z : Z) (hf : ∀ x, f x = z) :
    apm_t01a03_H1map f = 0 := by
  have hconst : f = ContinuousMap.const X z := by
    ext x
    exact hf x
  subst f
  exact
    ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_const_eq_zero
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero z

/-- A surjective map between two copies of `ℤ⁴` is injective. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_hopf
    {A B : ModuleCat ℤ} (_eA : A ≅ ModuleCat.of ℤ (Fin 4 → ℤ))
    (_eB : B ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) (f : A ⟶ B)
    (hf : Function.Surjective f) : Function.Injective f := by
  let g : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) :=
    (_eA.inv ≫ f ≫ _eB.hom).hom
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨b, hb⟩ :=
      (ConcreteCategory.bijective_of_isIso _eB.hom).2 y
    obtain ⟨a, ha⟩ := hf b
    refine ⟨_eA.hom a, ?_⟩
    change _eB.hom (f (_eA.inv (_eA.hom a))) = y
    simpa only [Iso.hom_inv_id_apply, ha, hb]
  have hgi : Function.Injective g :=
    Module.End.injective_of_surjective ℤ (Fin 4 → ℤ) hg
  intro x y hxy
  apply (ConcreteCategory.bijective_of_isIso _eA.hom).1
  apply hgi
  change _eB.hom (f (_eA.inv (_eA.hom x))) =
    _eB.hom (f (_eA.inv (_eA.hom y)))
  simpa using congrArg (fun z ↦ _eB.hom z) hxy

/-! #### `_aux_model_surj` by Mayer–Vietoris

Cover `X = OnePoint (PT ⊔ PT)` by `U = range coe` (a copy of `PT ⊔ PT`) and
`V = {∞} ∪` two punctured squares around the punctures (a wedge of two open
squares at `∞`, contractible). `H₁ V = 0`, and `H₀ (U ∩ V) → H₀ U` is injective
(each punctured square is path connected and lies in its own summand of `U`),
so the connecting map `H₁ X → H₀ (U ∩ V)` is zero and `H₁ U → H₁ X` is onto. -/

/-- A punctured open square around the puncture `(1, 1)` of the torus. -/
def apm_t01a03_separating_circle_H1_zero_aux_N : Set apm_t01a03_PuncturedTorus :=
  {x | dist ((x.1.1 : Circle) : ℂ) 1 < 1 ∧ dist ((x.1.2 : Circle) : ℂ) 1 < 1}

def apm_t01a03_separating_circle_H1_zero_aux_Nsum : Set apm_t01a03_TwoPuncturedTori :=
  Sum.inl '' apm_t01a03_separating_circle_H1_zero_aux_N ∪
    Sum.inr '' apm_t01a03_separating_circle_H1_zero_aux_N

/-- The finite part. -/
def apm_t01a03_separating_circle_H1_zero_aux_U :
    Set (OnePoint apm_t01a03_TwoPuncturedTori) :=
  Set.range ((↑) : apm_t01a03_TwoPuncturedTori → OnePoint apm_t01a03_TwoPuncturedTori)

/-- `∞` together with the two punctured squares. -/
def apm_t01a03_separating_circle_H1_zero_aux_V :
    Set (OnePoint apm_t01a03_TwoPuncturedTori) :=
  (((↑) : apm_t01a03_TwoPuncturedTori → OnePoint apm_t01a03_TwoPuncturedTori) ''
    apm_t01a03_separating_circle_H1_zero_aux_Nsumᶜ)ᶜ

/-- `V` is open: the complement of the two squares is closed in two compact
tori, so compact (`OnePoint.isOpen_compl_image_coe`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_open_aux_N_compl_compact :
    IsCompact apm_t01a03_separating_circle_H1_zero_aux_Nᶜ := by
  rw [Subtype.isCompact_iff]
  let K : Set apm_t01a03_Torus :=
    {x | 1 ≤ dist ((x.1 : Circle) : ℂ) 1 ∨
      1 ≤ dist ((x.2 : Circle) : ℂ) 1}
  have hKclosed : IsClosed K := by
    apply IsClosed.union
    · exact isClosed_le continuous_const
        (continuous_dist.comp₂
          (continuous_subtype_val.comp continuous_fst) continuous_const)
    · exact isClosed_le continuous_const
        (continuous_dist.comp₂
          (continuous_subtype_val.comp continuous_snd) continuous_const)
  have hKcompact : IsCompact K := hKclosed.isCompact
  have himage :
      ((↑) : apm_t01a03_PuncturedTorus → apm_t01a03_Torus) ''
          apm_t01a03_separating_circle_H1_zero_aux_Nᶜ = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ¬ (dist (((y : apm_t01a03_Torus).1 : Circle) : ℂ) 1 < 1 ∧
        dist (((y : apm_t01a03_Torus).2 : Circle) : ℂ) 1 < 1) at hy
      change 1 ≤ dist (((y : apm_t01a03_Torus).1 : Circle) : ℂ) 1 ∨
        1 ≤ dist (((y : apm_t01a03_Torus).2 : Circle) : ℂ) 1
      by_cases h : dist (((y : apm_t01a03_Torus).1 : Circle) : ℂ) 1 < 1
      · exact Or.inr (le_of_not_gt (fun h' ↦ hy ⟨h, h'⟩))
      · exact Or.inl (le_of_not_gt h)
    · intro hx
      have hne : x ≠ ((1 : Circle), (1 : Circle)) := by
        intro heq
        subst x
        norm_num [K] at hx
      refine ⟨⟨x, hne⟩, ?_, rfl⟩
      change ¬ (dist ((x.1 : Circle) : ℂ) 1 < 1 ∧
        dist ((x.2 : Circle) : ℂ) 1 < 1)
      rintro ⟨h1, h2⟩
      rcases hx with hx | hx
      · exact (not_lt_of_ge hx) h1
      · exact (not_lt_of_ge hx) h2
  rw [himage]
  exact hKcompact

lemma apm_t01a03_separating_circle_H1_zero_aux_V_open :
    IsOpen apm_t01a03_separating_circle_H1_zero_aux_V := by
  apply OnePoint.isOpen_compl_image_coe.mpr
  have hNc : IsCompact apm_t01a03_separating_circle_H1_zero_aux_Nᶜ :=
    apm_t01a03_separating_circle_H1_zero_aux_V_open_aux_N_compl_compact
  have hinl : IsCompact
      (Sum.inl '' apm_t01a03_separating_circle_H1_zero_aux_Nᶜ :
        Set apm_t01a03_TwoPuncturedTori) :=
    hNc.image continuous_inl
  have hinr : IsCompact
      (Sum.inr '' apm_t01a03_separating_circle_H1_zero_aux_Nᶜ :
        Set apm_t01a03_TwoPuncturedTori) :=
    hNc.image continuous_inr
  have heq : apm_t01a03_separating_circle_H1_zero_aux_Nsumᶜ =
      Sum.inl '' apm_t01a03_separating_circle_H1_zero_aux_Nᶜ ∪
        Sum.inr '' apm_t01a03_separating_circle_H1_zero_aux_Nᶜ := by
    ext x
    cases x <;> simp [apm_t01a03_separating_circle_H1_zero_aux_Nsum]
  rw [heq]
  exact ⟨(hinl.union hinr).isClosed, hinl.union hinr⟩

/-! #### `_aux_V_H1_zero` by a homeomorphism onto a star-shaped wedge

(split 2026-10-19, after a PARTIAL from lemma-1 that stalled on continuity of a
direct contraction at `∞`.) `V` is homeomorphic to `W`, two open sup-norm unit
squares in `(Fin 2 → ℝ) × (Fin 2 → ℝ)` meeting at the origin, with `∞ ↦ 0`.
`W` is star-shaped about `0`, so `V` is contractible. The chart on `N` is the
pair of angles scaled by `3/π`: `|z - 1| < 1` on the circle iff `|arg z| < π/3`.
Continuity at `∞` in both directions is carried by the two compactness clauses
of the chart, which `_aux_homeomorph` takes as hypotheses. -/

/-- Two open unit squares (sup norm) wedged at the origin. -/
def apm_t01a03_separating_circle_H1_zero_aux_W : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  Metric.ball 0 1 ×ˢ {0} ∪ {0} ×ˢ Metric.ball 0 1

/-- `W` is star-shaped about the origin (`StarConvex.contractibleSpace`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_W_contractible :
    ContractibleSpace apm_t01a03_separating_circle_H1_zero_aux_W := by
  have hball : StarConvex ℝ (0 : Fin 2 → ℝ) (Metric.ball 0 1) :=
    (convex_ball (0 : Fin 2 → ℝ) 1).starConvex (Metric.mem_ball_self zero_lt_one)
  have hsingleton : StarConvex ℝ (0 : Fin 2 → ℝ) ({0} : Set (Fin 2 → ℝ)) :=
    starConvex_singleton 0
  apply ((hball.prod hsingleton).union (hsingleton.prod hball)).contractibleSpace
  refine ⟨(0, 0), ?_⟩
  left
  exact ⟨Metric.mem_ball_self zero_lt_one, Set.mem_singleton 0⟩

lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angles_ne_zero
    (x : apm_t01a03_PuncturedTorus) :
    (fun i : Fin 2 => if i = 0 then Complex.arg (x.1.1 : ℂ)
      else Complex.arg (x.1.2 : ℂ)) ≠ 0 := by
  intro h
  have h0 : Complex.arg (x.1.1 : ℂ) = 0 := by
    have := congrFun h (0 : Fin 2)
    simpa using this
  have h1 : Complex.arg (x.1.2 : ℂ) = 0 := by
    have := congrFun h (1 : Fin 2)
    simpa using this
  apply x.2
  apply Prod.ext
  · exact Circle.injective_arg (by simpa using h0)
  · exact Circle.injective_arg (by simpa using h1)

/-- The scaled angle coordinates `(3/π)·(arg x₁, arg x₂)` of a point of the punctured
torus. On `N` they range over the punctured open unit square (sup norm). -/
noncomputable def apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle
    (x : apm_t01a03_PuncturedTorus) : Fin 2 → ℝ :=
  fun i => (3 / Real.pi) *
    (if i = 0 then Complex.arg (x.1.1 : ℂ) else Complex.arg (x.1.2 : ℂ))

/-- The chart: `N` is homeomorphic to the punctured open unit ball of `Fin 2 → ℝ`
(sup norm, so the open square `(-1,1)²` minus `0`) by the scaled angles. For
`z : Circle`, `dist z 1 < 1 ↔ |arg z| < π/3`; the inverse is
`θ ↦ (Circle.exp (π/3·θ₀), Circle.exp (π/3·θ₁))`; nonvanishing is
`_aux_angles_ne_zero`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_dist
    (z : Circle) :
    dist (z : ℂ) 1 < 1 ↔ |Complex.arg (z : ℂ)| < Real.pi / 3 := by
  have hzarg : |Complex.arg (z : ℂ)| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hsq : ‖(z : ℂ) - 1‖ ^ 2 = 2 * (1 - Real.cos |Complex.arg (z : ℂ)|) := by
    rw [Complex.sq_norm]
    rw [Complex.normSq_apply]
    have hre : (z : ℂ).re = Real.cos (Complex.arg (z : ℂ)) := by
      rw [Complex.cos_arg z.coe_ne_zero]
      simp
    have hcos : Real.cos |Complex.arg (z : ℂ)| =
        Real.cos (Complex.arg (z : ℂ)) := Real.cos_abs _
    rw [hcos, ← hre]
    rw [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    have hn := Circle.normSq_coe z
    rw [Complex.normSq_apply] at hn
    nlinarith
  rw [dist_eq_norm]
  constructor
  · intro h
    have hs : ‖(z : ℂ) - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg ((z : ℂ) - 1)]
    rw [hsq] at hs
    have hc : Real.cos (Real.pi / 3) < Real.cos |Complex.arg (z : ℂ)| := by
      rw [Real.cos_pi_div_three]
      linarith
    by_contra hn
    have hge : Real.pi / 3 ≤ |Complex.arg (z : ℂ)| := le_of_not_gt hn
    have hle : Real.cos |Complex.arg (z : ℂ)| ≤ Real.cos (Real.pi / 3) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) hzarg hge
    exact (not_lt_of_ge hle) hc
  · intro h
    have hc : Real.cos (Real.pi / 3) < Real.cos |Complex.arg (z : ℂ)| :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by nlinarith [Real.pi_pos]) h
    rw [Real.cos_pi_div_three] at hc
    have hs : ‖(z : ℂ) - 1‖ ^ 2 < 1 := by rw [hsq]; nlinarith
    nlinarith [norm_nonneg ((z : ℂ) - 1)]

lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_scale (z : Circle) :
    dist (z : ℂ) 1 < 1 ↔ |3 / Real.pi * Complex.arg (z : ℂ)| < 1 := by
  have hp := Real.pi_pos
  rw [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_dist, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 / Real.pi),
    div_mul_eq_mul_div, div_lt_one hp]
  constructor <;> intro h <;> linarith

lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_arg_exp {t : ℝ} (ht : |t| < 1) :
    Complex.arg ((Circle.exp (Real.pi / 3 * t) : Circle) : ℂ) = Real.pi / 3 * t := by
  have hp := Real.pi_pos
  rw [abs_lt] at ht
  apply Circle.arg_exp <;> nlinarith

lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_coord (θ : (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)))
    (i : Fin 2) : |(θ : Fin 2 → ℝ) i| < 1 := by
  have h := θ.2.1
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff zero_lt_one] at h
  simpa [Real.norm_eq_abs] using h i

lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo :
    ∃ φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
        (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)),
      ∀ x, (φ x : Fin 2 → ℝ) =
        apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x.1 := by
  have hp := Real.pi_pos
  have hmem : ∀ x : apm_t01a03_separating_circle_H1_zero_aux_N,
      apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x.1 ∈ (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)) := by
    intro x
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff zero_lt_one]
      intro i
      rw [Real.norm_eq_abs]
      fin_cases i
      · simpa [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle] using (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_scale _).1 x.2.1
      · simpa [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle] using (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_scale _).1 x.2.2
    · intro h
      rw [Set.mem_singleton_iff] at h
      apply apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angles_ne_zero x.1
      funext i
      have hi := congrFun h i
      simp only [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle, Pi.zero_apply] at hi ⊢
      exact (mul_eq_zero.1 hi).resolve_left (by positivity)
  have hne : ∀ θ : (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)),
      ((Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) 0),
        Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) 1)) : apm_t01a03_Torus) ≠
        ((1 : Circle), (1 : Circle)) := by
    intro θ h
    apply θ.2.2
    rw [Set.mem_singleton_iff]
    have hz : ∀ i, (θ : Fin 2 → ℝ) i = 0 := by
      intro i
      have key : ∀ j : Fin 2, Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) j) = 1 →
          (θ : Fin 2 → ℝ) j = 0 := by
        intro j hj
        have ha := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_arg_exp (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_coord θ j)
        rw [hj, Circle.coe_one, Complex.arg_one] at ha
        exact (mul_eq_zero.1 ha.symm).resolve_left (by positivity)
      fin_cases i
      · exact key 0 (congrArg Prod.fst h)
      · exact key 1 (congrArg Prod.snd h)
    funext i
    exact hz i
  have hN : ∀ θ : (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)),
      (⟨(Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) 0),
        Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) 1)), hne θ⟩ : apm_t01a03_PuncturedTorus) ∈
        apm_t01a03_separating_circle_H1_zero_aux_N := by
    intro θ
    have hc : ∀ j : Fin 2, dist ((Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) j) : Circle) : ℂ) 1 < 1 := by
      intro j
      rw [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_scale, apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_arg_exp (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_coord θ j)]
      have : 3 / Real.pi * (Real.pi / 3 * (θ : Fin 2 → ℝ) j) = (θ : Fin 2 → ℝ) j := by
        field_simp
      rw [this]
      exact apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_coord θ j
    exact ⟨hc 0, hc 1⟩
  have hcont : ∀ j : Fin 2, ContinuousOn Complex.arg {z : ℂ | dist z 1 < 1} := by
    intro _ z hz
    apply ContinuousAt.continuousWithinAt
    apply Complex.continuousAt_arg
    have h1 := Complex.mem_slitPlane_of_norm_lt_one (z := z - 1) (by rwa [← dist_eq_norm])
    simpa using h1
  refine ⟨{ toFun := fun x => ⟨apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x.1, hmem x⟩
            invFun := fun θ => ⟨⟨(Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) 0),
              Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) 1)), hne θ⟩, hN θ⟩
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun x => rfl⟩
  · intro x
    have e : ∀ a : ℝ, Real.pi / 3 * (3 / Real.pi * a) = a := by
      intro a; field_simp
    apply Subtype.ext; apply Subtype.ext
    apply Prod.ext
    · simp only [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle, if_true]
      rw [e, Circle.exp_arg]
    · simp only [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle, Fin.one_eq_zero_iff, if_false, OfNat.ofNat_ne_one]
      rw [e, Circle.exp_arg]
  · intro θ
    apply Subtype.ext
    funext i
    have e : ∀ a : ℝ, 3 / Real.pi * (Real.pi / 3 * a) = a := by
      intro a; field_simp
    by_cases hi : i = 0
    · subst hi
      show 3 / Real.pi * Complex.arg ((Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) 0) : Circle) : ℂ) =
        (θ : Fin 2 → ℝ) 0
      rw [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_arg_exp (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_coord θ 0), e]
    · obtain rfl : i = 1 := by fin_cases i <;> simp_all
      show 3 / Real.pi * Complex.arg ((Circle.exp (Real.pi / 3 * (θ : Fin 2 → ℝ) 1) : Circle) : ℂ) =
        (θ : Fin 2 → ℝ) 1
      rw [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_arg_exp (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo_aux_coord θ 1), e]
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_const.mul
    have c0 : Continuous fun x : apm_t01a03_separating_circle_H1_zero_aux_N =>
        Complex.arg ((x.1.1.1 : Circle) : ℂ) :=
      (hcont 0).comp_continuous (by fun_prop) (fun x => x.2.1)
    have c1 : Continuous fun x : apm_t01a03_separating_circle_H1_zero_aux_N =>
        Complex.arg ((x.1.1.2 : Circle) : ℂ) :=
      (hcont 1).comp_continuous (by fun_prop) (fun x => x.2.2)
    by_cases hi : i = 0
    · simpa [hi] using c0
    · simpa [hi] using c1
  · apply Continuous.subtype_mk
    have h0 : Continuous fun θ : (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)) => Real.pi / 3 * (θ : Fin 2 → ℝ) 0 :=
      continuous_const.mul ((continuous_apply 0).comp continuous_subtype_val)
    have h1 : Continuous fun θ : (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)) => Real.pi / 3 * (θ : Fin 2 → ℝ) 1 :=
      continuous_const.mul ((continuous_apply 1).comp continuous_subtype_val)
    apply Continuous.subtype_mk
    exact (Circle.exp.continuous.comp h0).prodMk (Circle.exp.continuous.comp h1)

/-- Away from the puncture the points of `N` lie in a compact set: for `ε > 0`,
take the image of the compact `{θ | ε ≤ ‖θ‖ ≤ 1}` under
`θ ↦ (Circle.exp (π/3·θ₀), Circle.exp (π/3·θ₁))` (it avoids `(1,1)` since
`0 < ‖θ‖ ≤ 1`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_far :
    ∀ ε > 0, ∃ C : Set apm_t01a03_PuncturedTorus, IsCompact C ∧
      ∀ x ∈ apm_t01a03_separating_circle_H1_zero_aux_N,
        ε ≤ ‖apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x‖ →
          x ∈ C := by
  intro ε hε
  let a : apm_t01a03_Torus → (Fin 2 → ℝ) := fun x i => (3 / Real.pi) *
    (if i = 0 then Complex.arg (x.1 : ℂ) else Complex.arg (x.2 : ℂ))
  have ha : ContinuousAt a ((1 : Circle), (1 : Circle)) := by
    apply continuousAt_pi.mpr
    intro i
    apply ContinuousAt.const_mul
    have harg1 : ContinuousAt Complex.arg (1 : ℂ) :=
      Complex.continuousAt_arg (by simp [Complex.slitPlane])
    split
    · simpa only [Function.comp_apply] using harg1.comp_of_eq
        (continuous_subtype_val.comp continuous_fst).continuousAt (by simp)
    · simpa only [Function.comp_apply] using harg1.comp_of_eq
        (continuous_subtype_val.comp continuous_snd).continuousAt (by simp)
  have ha0 : a ((1 : Circle), (1 : Circle)) = 0 := by
    ext i
    simp [a]
  have hanorm : ContinuousAt (fun y => ‖a y‖) ((1 : Circle), (1 : Circle)) := ha.norm
  rw [Metric.continuousAt_iff] at hanorm
  obtain ⟨δ, hδ, hsmall⟩ := hanorm ε hε
  let D : Set apm_t01a03_PuncturedTorus :=
    {x | δ ≤ dist (x.1 : apm_t01a03_Torus) ((1 : Circle), (1 : Circle))}
  refine ⟨D, ?_, ?_⟩
  · rw [(Topology.IsEmbedding.subtypeVal).isCompact_iff]
    have himage : ((↑) : apm_t01a03_PuncturedTorus → apm_t01a03_Torus) '' D =
        {y | δ ≤ dist y ((1 : Circle), (1 : Circle))} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        have hne : y ≠ ((1 : Circle), (1 : Circle)) := by
          intro heq
          subst y
          exact (not_le_of_gt hδ) (by simpa using hy)
        exact ⟨⟨y, hne⟩, hy, rfl⟩
    rw [himage]
    exact (isClosed_le continuous_const
      (continuous_id.dist continuous_const)).isCompact
  · intro x hx hfar
    change δ ≤ dist (x.1 : apm_t01a03_Torus) ((1 : Circle), (1 : Circle))
    by_contra hnot
    have hs := hsmall (lt_of_not_ge hnot)
    have hs' : ‖a (x.1 : apm_t01a03_Torus)‖ < ε := by
      simpa [ha0] using hs
    apply (not_lt_of_ge hfar)
    exact hs'

/-- A compact subset of the punctured torus misses a neighbourhood of the puncture:
its image in the torus is compact, hence closed, and omits `(1,1)`; small angles
put a point close to `(1,1)`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_near :
    ∀ C : Set apm_t01a03_PuncturedTorus, IsCompact C → ∃ r > 0,
      ∀ x ∈ apm_t01a03_separating_circle_H1_zero_aux_N,
        ‖apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x‖ < r →
          x ∉ C := by
  classical
  intro C hC
  let q : apm_t01a03_PuncturedTorus → apm_t01a03_Torus := fun x => x.1
  let K : Set apm_t01a03_Torus := q '' C
  have hK : IsCompact K := hC.image (by fun_prop)
  have hp : ((1 : Circle), (1 : Circle)) ∉ K := by
    rintro ⟨x, hx, heq⟩
    exact x.2 heq
  have hopen : IsOpen (Kᶜ) := hK.isClosed.isOpen_compl
  let f : (Fin 2 → ℝ) → apm_t01a03_Torus := fun θ =>
    (Circle.exp (Real.pi / 3 * θ 0), Circle.exp (Real.pi / 3 * θ 1))
  have hf : Continuous f := by
    apply Continuous.prodMk <;>
      exact Circle.exp.continuous.comp
        (continuous_const.mul (continuous_apply _))
  have hf0 : f 0 = ((1 : Circle), (1 : Circle)) := by
    simp [f]
  have hnhds : f ⁻¹' Kᶜ ∈ nhds (0 : Fin 2 → ℝ) := by
    apply hf.continuousAt.preimage_mem_nhds
    rw [hf0]
    exact hopen.mem_nhds hp
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨r, hr, ?_⟩
  intro x hxN hxsmall hxC
  have hfx : f
      (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x) =
      x.1 := by
    have e : ∀ a : ℝ, Real.pi / 3 * (3 / Real.pi * a) = a := by
      intro a
      field_simp
    apply Prod.ext
    · simp only [f,
        apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle,
        if_true]
      rw [e, Circle.exp_arg]
    · simp only [f,
        apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle,
        Fin.one_eq_zero_iff, if_false, OfNat.ofNat_ne_one]
      rw [e, Circle.exp_arg]
  have hball :
      apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x ∈
        Metric.ball (0 : Fin 2 → ℝ) r := by
    simpa [dist_zero_right] using hxsmall
  have hnotK := hrsub hball
  have hinK : f
      (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x) ∈ K := by
    rw [hfx]
    exact ⟨x, hxC, rfl⟩
  exact hnotK hinK

/-- A chart from the punctured square `N` onto the punctured open unit square,
`x ↦ (3/π) • (arg x₁, arg x₂)`. Points far from `0` in the chart lie in a
compact set of the punctured torus, and every compact set of the punctured
torus stays away from `0` in the chart. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart :
    ∃ φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
        (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)),
      (∀ ε > 0, ∃ C : Set apm_t01a03_PuncturedTorus, IsCompact C ∧
          ∀ x, ε ≤ ‖(φ x : Fin 2 → ℝ)‖ → (x : apm_t01a03_PuncturedTorus) ∈ C) ∧
      (∀ C : Set apm_t01a03_PuncturedTorus, IsCompact C → ∃ r > 0,
          ∀ x, ‖(φ x : Fin 2 → ℝ)‖ < r → (x : apm_t01a03_PuncturedTorus) ∉ C) := by
  obtain ⟨φ, hφ⟩ := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo
  refine ⟨φ, fun ε hε => ?_, fun C hC => ?_⟩
  · obtain ⟨C, hC, hmem⟩ :=
      apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_far ε hε
    exact ⟨C, hC, fun x hx => hmem x.1 x.2 (by rwa [hφ] at hx)⟩
  · obtain ⟨r, hr, hnot⟩ :=
      apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_near C hC
    exact ⟨r, hr, fun x hx => hnot x.1 x.2 (by rwa [hφ] at hx)⟩

/-- Gluing two copies of a chart at `∞ ↦ 0`: `∞ ↦ 0`, `inl x ↦ (φ x, 0)`,
`inr x ↦ (0, φ x)`. Continuity at `∞` uses the first compactness clause, and
continuity of the inverse at `0` uses the second. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem
    (p : apm_t01a03_TwoPuncturedTori)
    (hp : (p : OnePoint apm_t01a03_TwoPuncturedTori) ∈
      apm_t01a03_separating_circle_H1_zero_aux_V) :
    p ∈ apm_t01a03_separating_circle_H1_zero_aux_Nsum := by
  by_contra hn
  exact hp ⟨p, hn, rfl⟩

noncomputable def
    apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward
    (φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ))) :
    apm_t01a03_separating_circle_H1_zero_aux_V →
      apm_t01a03_separating_circle_H1_zero_aux_W := fun ⟨z, hz⟩ => by
  classical
  induction z using OnePoint.rec with
  | infty =>
      exact ⟨(0, 0), Or.inl ⟨Metric.mem_ball_self zero_lt_one, rfl⟩⟩
  | coe p =>
      have hp :=
        apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem p hz
      cases p with
      | inl p =>
          have hpN : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hp
          let q := φ ⟨p, hpN⟩
          exact ⟨((q : Fin 2 → ℝ), 0), Or.inl ⟨q.2.1, rfl⟩⟩
      | inr p =>
          have hpN : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hp
          let q := φ ⟨p, hpN⟩
          exact ⟨(0, (q : Fin 2 → ℝ)), Or.inr ⟨rfl, q.2.1⟩⟩

/-- The glued map is a bijection `V → W`: `∞` is the only point sent to
`(0, 0)` (`φ` takes values off `0`), the two summands land in the two different
squares, and on each summand it is `φ`, which is a bijection onto the punctured
square. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_bijective
    (φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ))) :
    Function.Bijective (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ) := by
  classical
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    induction x using OnePoint.rec with
    | infty =>
        induction y using OnePoint.rec with
        | infty => rfl
        | coe q =>
            cases q with
            | inl q =>
                have hq :=
                  apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem
                    (Sum.inl q) hy
                have hqN : q ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
                  simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hq
                have hn : (φ ⟨q, hqN⟩ : Fin 2 → ℝ) ≠ 0 := by
                  exact fun h => (φ ⟨q, hqN⟩).2.2 (Set.mem_singleton_iff.mpr h)
                have := congrArg (fun z : apm_t01a03_separating_circle_H1_zero_aux_W => z.1.1) hxy
                simp [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward] at this
                exact (hn this.symm).elim
            | inr q =>
                have hq :=
                  apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem
                    (Sum.inr q) hy
                have hqN : q ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
                  simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hq
                have hn : (φ ⟨q, hqN⟩ : Fin 2 → ℝ) ≠ 0 := by
                  exact fun h => (φ ⟨q, hqN⟩).2.2 (Set.mem_singleton_iff.mpr h)
                have := congrArg (fun z : apm_t01a03_separating_circle_H1_zero_aux_W => z.1.2) hxy
                simp [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward] at this
                exact (hn this.symm).elim
    | coe p =>
        induction y using OnePoint.rec with
        | infty =>
            cases p with
            | inl p =>
                have hp := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem (Sum.inl p) hx
                have hpN : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
                  simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hp
                have hn : (φ ⟨p, hpN⟩ : Fin 2 → ℝ) ≠ 0 := fun h =>
                  (φ ⟨p, hpN⟩).2.2 (Set.mem_singleton_iff.mpr h)
                have he := congrArg (fun z : apm_t01a03_separating_circle_H1_zero_aux_W => z.1.1) hxy
                simp [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward] at he
                exact (hn he).elim
            | inr p =>
                have hp := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem (Sum.inr p) hx
                have hpN : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
                  simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hp
                have hn : (φ ⟨p, hpN⟩ : Fin 2 → ℝ) ≠ 0 := fun h =>
                  (φ ⟨p, hpN⟩).2.2 (Set.mem_singleton_iff.mpr h)
                have he := congrArg (fun z : apm_t01a03_separating_circle_H1_zero_aux_W => z.1.2) hxy
                simp [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward] at he
                exact (hn he).elim
        | coe q =>
            apply Subtype.ext
            cases p with
            | inl p =>
                cases q with
                | inl q =>
                    simp only [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward] at hxy
                    have hpN := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem (Sum.inl p) hx
                    have hqN := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem (Sum.inl q) hy
                    simp [apm_t01a03_separating_circle_H1_zero_aux_Nsum] at hpN hqN
                    have he := congrArg (fun z : apm_t01a03_separating_circle_H1_zero_aux_W => z.1.1) hxy
                    exact congrArg (fun s : apm_t01a03_TwoPuncturedTori =>
                      (s : OnePoint apm_t01a03_TwoPuncturedTori))
                        (congrArg Sum.inl (congrArg Subtype.val (φ.injective (Subtype.ext he))))
                | inr q =>
                    simp only [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward] at hxy
                    have hpN := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem (Sum.inl p) hx
                    simp [apm_t01a03_separating_circle_H1_zero_aux_Nsum] at hpN
                    have hn : (φ ⟨p, hpN⟩ : Fin 2 → ℝ) ≠ 0 := fun h =>
                      (φ ⟨p, hpN⟩).2.2 (Set.mem_singleton_iff.mpr h)
                    exact (hn (congrArg (fun z : apm_t01a03_separating_circle_H1_zero_aux_W => z.1.1) hxy)).elim
            | inr p =>
                cases q with
                | inl q =>
                    simp only [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward] at hxy
                    have hqN := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem (Sum.inl q) hy
                    simp [apm_t01a03_separating_circle_H1_zero_aux_Nsum] at hqN
                    have hn : (φ ⟨q, hqN⟩ : Fin 2 → ℝ) ≠ 0 := fun h =>
                      (φ ⟨q, hqN⟩).2.2 (Set.mem_singleton_iff.mpr h)
                    exact (hn (congrArg (fun z : apm_t01a03_separating_circle_H1_zero_aux_W => z.1.1) hxy).symm).elim
                | inr q =>
                    simp only [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward] at hxy
                    have hpN := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem (Sum.inr p) hx
                    have hqN := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem (Sum.inr q) hy
                    simp [apm_t01a03_separating_circle_H1_zero_aux_Nsum] at hpN hqN
                    have he := congrArg (fun z : apm_t01a03_separating_circle_H1_zero_aux_W => z.1.2) hxy
                    exact congrArg (fun s : apm_t01a03_TwoPuncturedTori =>
                      (s : OnePoint apm_t01a03_TwoPuncturedTori))
                        (congrArg Sum.inr (congrArg Subtype.val (φ.injective (Subtype.ext he))))
  · rintro ⟨⟨a, b⟩, hab⟩
    rcases hab with hab | hab
    · rcases hab with ⟨ha, hb0⟩
      by_cases hzero : a = 0
      ·
        refine ⟨⟨(OnePoint.infty : OnePoint apm_t01a03_TwoPuncturedTori), ?_⟩, ?_⟩
        · simp [apm_t01a03_separating_circle_H1_zero_aux_V]
        · apply Subtype.ext
          change (0, 0) = (a, b)
          exact Prod.ext hzero.symm (Set.mem_singleton_iff.mp hb0).symm
      · let q : (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)) :=
          ⟨a, ha, fun h => hzero (Set.mem_singleton_iff.mp h)⟩
        let p := (φ.symm q : apm_t01a03_separating_circle_H1_zero_aux_N)
        have hpV : ((Sum.inl p.1 : apm_t01a03_TwoPuncturedTori) :
            OnePoint apm_t01a03_TwoPuncturedTori) ∈ apm_t01a03_separating_circle_H1_zero_aux_V := by
          rintro ⟨z, hz, heq⟩
          have heq' : z = Sum.inl p.1 := OnePoint.coe_injective heq
          subst z
          exact hz (by
            simp [apm_t01a03_separating_circle_H1_zero_aux_Nsum])
        refine ⟨⟨(Sum.inl p.1 : apm_t01a03_TwoPuncturedTori), hpV⟩, ?_⟩
        apply Subtype.ext
        change ((φ p : Fin 2 → ℝ), 0) = (a, b)
        exact Prod.ext (by simp [p, q]) (Set.mem_singleton_iff.mp hb0).symm
    · rcases hab with ⟨ha0, hb⟩
      by_cases hzero : b = 0
      ·
        refine ⟨⟨(OnePoint.infty : OnePoint apm_t01a03_TwoPuncturedTori), ?_⟩, ?_⟩
        · simp [apm_t01a03_separating_circle_H1_zero_aux_V]
        · apply Subtype.ext
          change (0, 0) = (a, b)
          exact Prod.ext (Set.mem_singleton_iff.mp ha0).symm hzero.symm
      · let q : (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)) :=
          ⟨b, hb, fun h => hzero (Set.mem_singleton_iff.mp h)⟩
        let p := (φ.symm q : apm_t01a03_separating_circle_H1_zero_aux_N)
        have hpV : ((Sum.inr p.1 : apm_t01a03_TwoPuncturedTori) :
            OnePoint apm_t01a03_TwoPuncturedTori) ∈ apm_t01a03_separating_circle_H1_zero_aux_V := by
          rintro ⟨z, hz, heq⟩
          have heq' : z = Sum.inr p.1 := OnePoint.coe_injective heq
          subst z
          exact hz (by
            simp [apm_t01a03_separating_circle_H1_zero_aux_Nsum])
        refine ⟨⟨(Sum.inr p.1 : apm_t01a03_TwoPuncturedTori), hpV⟩, ?_⟩
        apply Subtype.ext
        change (0, (φ p : Fin 2 → ℝ)) = (a, b)
        exact Prod.ext (Set.mem_singleton_iff.mp ha0).symm (by simp [p, q])

/-- The glued map is continuous. At a finite point of `V` it is `φ` on an open
piece (`OnePoint.isOpenEmbedding_coe`, and `Nsum` is open). At `∞`: a
neighbourhood of `(0, 0)` in `W` contains every point of norm `< ε`; by `hfar`,
the points of either summand with `‖φ x‖ ≥ ε` lie in a compact set `C`, so the
preimage contains the open set `V \ (inl '' C ∪ inr '' C)`, a neighbourhood of
`∞` (`OnePoint.isOpen_compl_image_coe`-style). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_continuous
    (φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)))
    (hfar : ∀ ε > 0, ∃ C : Set apm_t01a03_PuncturedTorus, IsCompact C ∧
          ∀ x, ε ≤ ‖(φ x : Fin 2 → ℝ)‖ → (x : apm_t01a03_PuncturedTorus) ∈ C) :
    Continuous (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ) := by
  classical
  rw [continuous_iff_continuousAt]
  rintro ⟨z, hz⟩
  induction z using OnePoint.rec with
  | infty =>
      rw [ContinuousAt, tendsto_subtype_rng]
      intro s hs
      obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
      obtain ⟨C, hC, hfarC⟩ := hfar ε hε
      let K : Set apm_t01a03_TwoPuncturedTori := Sum.inl '' C ∪ Sum.inr '' C
      have hK : IsCompact K :=
        (hC.image continuous_inl).union (hC.image continuous_inr)
      let O : Set (OnePoint apm_t01a03_TwoPuncturedTori) :=
        (((↑) : apm_t01a03_TwoPuncturedTori →
          OnePoint apm_t01a03_TwoPuncturedTori) '' K)ᶜ
      have hOopen : IsOpen O := by
        exact OnePoint.isOpen_compl_image_coe.mpr ⟨hK.isClosed, hK⟩
      have hinfO : OnePoint.infty ∈ O := by
        simp [O]
      change (fun x =>
        (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward
          φ x : (Fin 2 → ℝ) × (Fin 2 → ℝ))) ⁻¹' s ∈ nhds ⟨OnePoint.infty, hz⟩
      refine Filter.mem_of_superset
        ((hOopen.preimage continuous_subtype_val).mem_nhds hinfO) ?_
      rintro ⟨w, hwV⟩ hwO
      induction w using OnePoint.rec with
      | infty =>
          apply hεs
          simpa [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward]
      | coe p =>
          have hpN :=
            apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem p hwV
          cases p with
          | inl p =>
              have hpN' : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
                simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hpN
              have hpC : p ∉ C := by
                intro hpC
                exact hwO ⟨Sum.inl p, Or.inl ⟨p, hpC, rfl⟩, rfl⟩
              have hnorm : ‖(φ ⟨p, hpN'⟩ : Fin 2 → ℝ)‖ < ε :=
                lt_of_not_ge (fun h ↦ hpC (hfarC ⟨p, hpN'⟩ h))
              apply hεs
              change dist ((φ ⟨p, hpN'⟩ : Fin 2 → ℝ), 0) (0, 0) < ε
              simpa [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward,
                dist_eq_norm] using hnorm
          | inr p =>
              have hpN' : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
                simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hpN
              have hpC : p ∉ C := by
                intro hpC
                exact hwO ⟨Sum.inr p, Or.inr ⟨p, hpC, rfl⟩, rfl⟩
              have hnorm : ‖(φ ⟨p, hpN'⟩ : Fin 2 → ℝ)‖ < ε :=
                lt_of_not_ge (fun h ↦ hpC (hfarC ⟨p, hpN'⟩ h))
              apply hεs
              change dist (0, (φ ⟨p, hpN'⟩ : Fin 2 → ℝ)) (0, 0) < ε
              simpa [apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward,
                dist_eq_norm] using hnorm
  | coe p =>
      cases p with
      | inl p =>
          have hpN :=
            apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem
              (Sum.inl p) hz
          have hpN' : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hpN
          let j : apm_t01a03_separating_circle_H1_zero_aux_N →
              apm_t01a03_separating_circle_H1_zero_aux_V := fun x =>
            ⟨((Sum.inl (x : apm_t01a03_PuncturedTorus) :
              apm_t01a03_TwoPuncturedTori) :
                OnePoint apm_t01a03_TwoPuncturedTori), by
              simpa [apm_t01a03_separating_circle_H1_zero_aux_V] using
                (show Sum.inl (x : apm_t01a03_PuncturedTorus) ∈
                    apm_t01a03_separating_circle_H1_zero_aux_Nsum from
                  Or.inl ⟨_, x.2, rfl⟩)⟩
          have hNopen : IsOpen apm_t01a03_separating_circle_H1_zero_aux_N := by
            exact (isOpen_lt
              ((continuous_subtype_val.comp continuous_fst).comp
                continuous_subtype_val |>.dist continuous_const) continuous_const).and
              (isOpen_lt
                ((continuous_subtype_val.comp continuous_snd).comp
                  continuous_subtype_val |>.dist continuous_const) continuous_const)
          have hj : Topology.IsOpenEmbedding j := by
            have he : Topology.IsOpenEmbedding (fun x : apm_t01a03_separating_circle_H1_zero_aux_N =>
                ((Sum.inl (x : apm_t01a03_PuncturedTorus) :
                  apm_t01a03_TwoPuncturedTori) : OnePoint apm_t01a03_TwoPuncturedTori)) :=
              OnePoint.isOpenEmbedding_coe.comp
                (Topology.IsOpenEmbedding.inl.comp hNopen.isOpenEmbedding_subtypeVal)
            refine ⟨he.isEmbedding.codRestrict
                apm_t01a03_separating_circle_H1_zero_aux_V (fun x => (j x).2), ?_⟩
            exact (he.isOpenMap.codRestrict (fun x => (j x).2)).isOpen_range
          let k : apm_t01a03_separating_circle_H1_zero_aux_N →
              apm_t01a03_separating_circle_H1_zero_aux_W := fun x =>
            ⟨((φ x : Fin 2 → ℝ), 0), Or.inl ⟨(φ x).2.1, rfl⟩⟩
          have hk : Continuous k := by
            dsimp [k]
            fun_prop
          have hh := (hj.continuousAt_iff
            (g := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ)
            (x := ⟨p, hpN'⟩)).mp (by
              have heq :
                  apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ ∘ j = k := by
                funext x
                apply Subtype.ext
                rfl
              rw [heq]
              exact hk.continuousAt)
          simpa [j] using hh
      | inr p =>
          have hpN :=
            apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem
              (Sum.inr p) hz
          have hpN' : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hpN
          let j : apm_t01a03_separating_circle_H1_zero_aux_N →
              apm_t01a03_separating_circle_H1_zero_aux_V := fun x =>
            ⟨((Sum.inr (x : apm_t01a03_PuncturedTorus) :
              apm_t01a03_TwoPuncturedTori) :
                OnePoint apm_t01a03_TwoPuncturedTori), by
              simpa [apm_t01a03_separating_circle_H1_zero_aux_V] using
                (show Sum.inr (x : apm_t01a03_PuncturedTorus) ∈
                    apm_t01a03_separating_circle_H1_zero_aux_Nsum from
                  Or.inr ⟨_, x.2, rfl⟩)⟩
          have hNopen : IsOpen apm_t01a03_separating_circle_H1_zero_aux_N := by
            exact (isOpen_lt
              ((continuous_subtype_val.comp continuous_fst).comp
                continuous_subtype_val |>.dist continuous_const) continuous_const).and
              (isOpen_lt
                ((continuous_subtype_val.comp continuous_snd).comp
                  continuous_subtype_val |>.dist continuous_const) continuous_const)
          have hj : Topology.IsOpenEmbedding j := by
            have he : Topology.IsOpenEmbedding (fun x : apm_t01a03_separating_circle_H1_zero_aux_N =>
                ((Sum.inr (x : apm_t01a03_PuncturedTorus) :
                  apm_t01a03_TwoPuncturedTori) : OnePoint apm_t01a03_TwoPuncturedTori)) :=
              OnePoint.isOpenEmbedding_coe.comp
                (Topology.IsOpenEmbedding.inr.comp hNopen.isOpenEmbedding_subtypeVal)
            refine ⟨he.isEmbedding.codRestrict
                apm_t01a03_separating_circle_H1_zero_aux_V (fun x => (j x).2), ?_⟩
            exact (he.isOpenMap.codRestrict (fun x => (j x).2)).isOpen_range
          let k : apm_t01a03_separating_circle_H1_zero_aux_N →
              apm_t01a03_separating_circle_H1_zero_aux_W := fun x =>
            ⟨(0, (φ x : Fin 2 → ℝ)), Or.inr ⟨rfl, (φ x).2.1⟩⟩
          have hk : Continuous k := by
            dsimp [k]
            fun_prop
          have hh := (hj.continuousAt_iff
            (g := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ)
            (x := ⟨p, hpN'⟩)).mp (by
              have heq :
                  apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ ∘ j = k := by
                funext x
                apply Subtype.ext
                rfl
              rw [heq]
              exact hk.continuousAt)
          simpa [j] using hh

/-- Openness at a finite point. Near `p ∈ Nsum` the glued map is `φ` on one
summand followed by the embedding of the punctured square into `W`; `Nsum` is
open in `PT ⊔ PT` (`OnePoint.isOpenEmbedding_coe`), so a neighbourhood of `p`
in `V` contains the image of a neighbourhood of `p` in its summand's `N`, which
`φ` (a homeomorphism) carries onto a neighbourhood of `φ p` in the punctured
square, and that square is open in `W` away from the origin. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_isOpenMap_aux_coe
    (φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)))
    (p : apm_t01a03_TwoPuncturedTori)
    (hp : (p : OnePoint apm_t01a03_TwoPuncturedTori) ∈
      apm_t01a03_separating_circle_H1_zero_aux_V) :
    nhds (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ ⟨p, hp⟩) ≤
      Filter.map (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ) (nhds ⟨p, hp⟩) := by
  sorry

/-- Openness at `∞`. A neighbourhood of `∞` in `V` contains `V` minus the image
of a compact `K ⊆ PT ⊔ PT`; write `K ⊆ inl '' C ∪ inr '' C` with `C` compact
(the two preimages, union). `hnear C` gives `r > 0` with every `x ∈ N` of
`‖φ x‖ < r` outside `C`; so every point of `W` of norm `< r` is the image of a
point of the neighbourhood (the origin is the image of `∞`, and `(q, 0)`,
`(0, q)` with `q ≠ 0` are images of `φ.symm q` in a summand). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_isOpenMap_aux_infty
    (φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)))
    (hnear : ∀ C : Set apm_t01a03_PuncturedTorus, IsCompact C → ∃ r > 0,
          ∀ x, ‖(φ x : Fin 2 → ℝ)‖ < r → (x : apm_t01a03_PuncturedTorus) ∉ C)
    (h : (OnePoint.infty : OnePoint apm_t01a03_TwoPuncturedTori) ∈
      apm_t01a03_separating_circle_H1_zero_aux_V) :
    nhds (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ ⟨OnePoint.infty, h⟩) ≤
      Filter.map (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ) (nhds ⟨OnePoint.infty, h⟩) := by
  classical
  rw [Filter.le_def]
  intro s hs
  rw [Filter.mem_map] at hs
  obtain ⟨u, hu, hus⟩ :=
    (mem_nhds_subtype
      apm_t01a03_separating_circle_H1_zero_aux_V ⟨OnePoint.infty, h⟩
      ((apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ) ⁻¹' s)).mp hs
  obtain ⟨K, ⟨hKclosed, hKcompact⟩, hKu⟩ :=
    OnePoint.hasBasis_nhds_infty.mem_iff.mp hu
  let fold : apm_t01a03_TwoPuncturedTori → apm_t01a03_PuncturedTorus :=
    Sum.elim id id
  let C : Set apm_t01a03_PuncturedTorus := fold '' K
  have hfold : Continuous fold := by
    apply continuous_sum_dom.mpr
    exact ⟨continuous_id, continuous_id⟩
  have hCcompact : IsCompact C := hKcompact.image hfold
  obtain ⟨r, hr, hsmall⟩ := hnear C hCcompact
  have hzero :
      apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ
          ⟨OnePoint.infty, h⟩ ∈ s := by
    apply hus
    apply hKu
    simp
  refine Metric.mem_nhds_iff.mpr ⟨r, hr, ?_⟩
  rintro z hz
  obtain ⟨x, rfl⟩ :=
    (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_bijective φ).2 z
  rcases x with ⟨x, hxV⟩
  induction x using OnePoint.rec with
  | infty => exact hzero
  | coe p =>
      apply hus
      apply hKu
      simp only [Set.mem_union, Set.mem_image, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      left
      refine ⟨p, ?_, rfl⟩
      intro hpK
      have hpC : fold p ∈ C := ⟨p, hpK, rfl⟩
      cases p with
      | inl p =>
          have hpN :=
            apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem
              (Sum.inl p) hxV
          have hpN' : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hpN
          have hnorm : ‖(φ ⟨p, hpN'⟩ : Fin 2 → ℝ)‖ < r := by
            let zin : apm_t01a03_separating_circle_H1_zero_aux_W :=
              ⟨((φ ⟨p, hpN'⟩ : Fin 2 → ℝ), 0), Or.inl ⟨(φ ⟨p, hpN'⟩).2.1, rfl⟩⟩
            let zzero : apm_t01a03_separating_circle_H1_zero_aux_W :=
              ⟨(0, 0), Or.inl ⟨Metric.mem_ball_self zero_lt_one, rfl⟩⟩
            have hin :
                apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ
                  ⟨((Sum.inl p : apm_t01a03_TwoPuncturedTori) :
                    OnePoint apm_t01a03_TwoPuncturedTori), hxV⟩ = zin := by
              apply Subtype.ext
              unfold apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward
              dsimp [zin]
              congr
            have hzero' :
                apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ
                  ⟨OnePoint.infty, h⟩ = zzero := by
              apply Subtype.ext
              rfl
            rw [hin, hzero'] at hz
            dsimp [zin, zzero] at hz
            rw [Metric.mem_ball] at hz
            rw [Subtype.dist_eq] at hz
            simpa [dist_eq_norm] using hz
          exact hsmall ⟨p, hpN'⟩ hnorm (by simpa [fold] using hpC)
      | inr p =>
          have hpN :=
            apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_mem
              (Sum.inr p) hxV
          have hpN' : p ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hpN
          have hnorm : ‖(φ ⟨p, hpN'⟩ : Fin 2 → ℝ)‖ < r := by
            let zin : apm_t01a03_separating_circle_H1_zero_aux_W :=
              ⟨(0, (φ ⟨p, hpN'⟩ : Fin 2 → ℝ)), Or.inr ⟨rfl, (φ ⟨p, hpN'⟩).2.1⟩⟩
            let zzero : apm_t01a03_separating_circle_H1_zero_aux_W :=
              ⟨(0, 0), Or.inl ⟨Metric.mem_ball_self zero_lt_one, rfl⟩⟩
            have hin :
                apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ
                  ⟨((Sum.inr p : apm_t01a03_TwoPuncturedTori) :
                    OnePoint apm_t01a03_TwoPuncturedTori), hxV⟩ = zin := by
              apply Subtype.ext
              unfold apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward
              dsimp [zin]
              congr
            have hzero' :
                apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ
                  ⟨OnePoint.infty, h⟩ = zzero := by
              apply Subtype.ext
              rfl
            rw [hin, hzero'] at hz
            dsimp [zin, zzero] at hz
            rw [Metric.mem_ball] at hz
            rw [Subtype.dist_eq] at hz
            simpa [dist_eq_norm] using hz
          exact hsmall ⟨p, hpN'⟩ hnorm (by simpa [fold] using hpC)

/-- The glued map is open: it is open at every point (`isOpenMap_iff_nhds_le`),
at `∞` by `_aux_infty` and at finite points by `_aux_coe`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_isOpenMap
    (φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)))
    (hnear : ∀ C : Set apm_t01a03_PuncturedTorus, IsCompact C → ∃ r > 0,
          ∀ x, ‖(φ x : Fin 2 → ℝ)‖ < r → (x : apm_t01a03_PuncturedTorus) ∉ C) :
    IsOpenMap (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ) := by
  rw [isOpenMap_iff_nhds_le]
  rintro ⟨z, hz⟩
  induction z using OnePoint.rec with
  | infty => exact apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_isOpenMap_aux_infty φ hnear hz
  | coe p => exact apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_isOpenMap_aux_coe φ p hz

lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph
    (φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
        (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)))
    (hfar : ∀ ε > 0, ∃ C : Set apm_t01a03_PuncturedTorus, IsCompact C ∧
          ∀ x, ε ≤ ‖(φ x : Fin 2 → ℝ)‖ → (x : apm_t01a03_PuncturedTorus) ∈ C)
    (hnear : ∀ C : Set apm_t01a03_PuncturedTorus, IsCompact C → ∃ r > 0,
          ∀ x, ‖(φ x : Fin 2 → ℝ)‖ < r → (x : apm_t01a03_PuncturedTorus) ∉ C) :
    Nonempty (apm_t01a03_separating_circle_H1_zero_aux_V ≃ₜ
      apm_t01a03_separating_circle_H1_zero_aux_W) :=
  ⟨(Equiv.ofBijective _ (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_bijective φ)).toHomeomorphOfContinuousOpen
    (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_continuous φ hfar) (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_isOpenMap φ hnear)⟩

/-- `H₁ V = 0`: `V` is two open squares wedged at their centres (`∞`), hence
contractible (`CoefficientContractiblePair.higher_zero`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero :
    Limits.IsZero (IntegralMV.HZ 1 apm_t01a03_separating_circle_H1_zero_aux_V) := by
  obtain ⟨φ, hfar, hnear⟩ := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart
  obtain ⟨e⟩ :=
    apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph φ hfar hnear
  haveI := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_W_contractible
  haveI : ContractibleSpace apm_t01a03_separating_circle_H1_zero_aux_V :=
    e.contractibleSpace
  exact ConstructionTargets.CoefficientContractiblePair.higher_zero ℤ _ 1 one_ne_zero

/-- The punctured square is path connected (lemma-3, round 2). In angle
coordinates it is the open square `(-π/3, π/3)²` minus its centre. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_N_pathConnected :
    PathConnectedSpace apm_t01a03_separating_circle_H1_zero_aux_N := by
  obtain ⟨φ, _, _⟩ :=
    apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart
  let e : (Fin 2 → ℝ) ≃ₜ Metric.ball (0 : Fin 2 → ℝ) 1 :=
    Homeomorph.unitBall
  have hrank : 1 < Module.rank ℝ (Fin 2 → ℝ) := by
    rw [← Module.finrank_eq_rank']
    norm_num [Module.finrank_fintype_fun_eq_card]
  have hpc : IsPathConnected (({0}ᶜ : Set (Fin 2 → ℝ))) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  have himage : (fun x ↦ (e x : Fin 2 → ℝ)) ''
      ({0}ᶜ : Set (Fin 2 → ℝ)) =
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(e x).property, ?_⟩
      intro h
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
      rw [Set.mem_singleton_iff] at h
      apply hx
      apply e.injective
      apply Subtype.ext
      exact h.trans (by simp [e])
    · intro hy
      refine ⟨e.symm ⟨y, hy.1⟩, ?_, ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      apply hy.2
      have := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy.1⟩)
      simpa [h, e] using this.symm
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy.1⟩)
  have hpc' : IsPathConnected
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0}) := by
    rw [← himage]
    exact hpc.image (e.continuous.subtype_val)
  haveI : PathConnectedSpace
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)) := by
    exact isPathConnected_iff_pathConnectedSpace.mp hpc'
  exact φ.symm.surjective.pathConnectedSpace φ.symm.continuous

/-- A map that reflects path-joinedness is injective on integral `H₀`.
(`H₀ A` is free on the path components of `A`; one route: for each path
component `K` of the target, counting the vertices of a `0`-chain that lie in `K`
kills boundaries, and these counts separate the vertex classes
`CoefficientH0.singularVertexH0Class` of distinct source components.) -/
noncomputable def apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B))
    (b : B) : Option A := by
  classical
  exact if h : ∃ a : A, Joined (f a) b then some (Classical.choose h) else none

set_option maxHeartbeats 800000

noncomputable def apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_vertex
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B))
    (b : B) : ModuleCat.of ℤ ℤ ⟶
      ConstructionTargets.CoefficientH0.SingularHomology ℤ 0 (TopCat.of A) :=
  match apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick f b with
  | some a => ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ a
  | none => 0

lemma apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick_spec
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B))
    {b : B} {a : A}
    (h : apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick f b = some a) :
    Joined (f a) b := by
  classical
  unfold apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick at h
  split at h <;> simp_all
  subst a
  exact Classical.choose_spec ‹∃ a, Joined (f a) b›

noncomputable def apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_chains
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) :
    (ConstructionTargets.CoefficientH0.SingularChains ℤ (TopCat.of B)).X 0 ⟶
      ConstructionTargets.CoefficientH0.SingularHomology ℤ 0 (TopCat.of A) := by
  change (∐ fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
    (TopCat.of B) 0 ↦ ModuleCat.of ℤ ℤ) ⟶ _
  exact Limits.Sigma.desc fun s =>
    apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_vertex
      f (ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint s)

lemma apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B))
    (hf : ∀ a a' : A, Joined (f a) (f a') → Joined a a') :
    Function.Injective (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ f) 0).hom := by
  classical
  open ConstructionTargets.CoefficientH0 in
    let KA := SingularChains ℤ (TopCat.of A)
    let KB := SingularChains ℤ (TopCat.of B)
    let v := apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_vertex f
    let L := apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_chains f
    have hv_joined {b b' : B} (hbb' : Joined b b') : v b = v b' := by
      dsimp [v, apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_vertex]
      generalize hp : apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick f b = p
      generalize hq : apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick f b' = q
      cases p with
      | none =>
          cases q with
          | none => rfl
          | some a' =>
              exfalso
              have ha' : Joined (f a') b' := by
                exact apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick_spec f hq
              have hex : ∃ a : A, Joined (f a) b :=
                ⟨a', ha'.trans hbb'.symm⟩
              simp [apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick,
                hex] at hp
      | some a =>
          cases q with
          | none =>
              exfalso
              have ha : Joined (f a) b := by
                exact apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick_spec f hp
              have hex : ∃ a' : A, Joined (f a') b' :=
                ⟨a, ha.trans hbb'⟩
              simp [apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick,
                hex] at hq
          | some a' =>
              apply singularVertexH0Class_eq_of_path ℤ
              apply (hf a a' ?_).somePath
              have ha : Joined (f a) b := by
                exact apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick_spec f hp
              have ha' : Joined (f a') b' := by
                exact apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick_spec f hq
              exact ha.trans (hbb'.trans ha'.symm)
    have hd : KB.d 1 0 ≫ L = 0 := by
      apply Limits.Sigma.hom_ext
      intro s
      change singularGenerator ℤ (TopCat.of B) 1 s ≫ KB.d 1 0 ≫ L = 0
      rw [← CategoryTheory.Category.assoc, singularGenerator_boundary ℤ,
        Fin.sum_univ_two, CategoryTheory.Preadditive.add_comp,
        CategoryTheory.Preadditive.zsmul_comp]
      norm_num
      dsimp [L,
        apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_chains,
        singularGenerator]
      erw [Limits.Sigma.ι_desc]
      change v _ + -(singularGenerator ℤ (TopCat.of B) 0
        ((TopCat.toSSet.obj (TopCat.of B)).δ (1 : Fin 2) s) ≫ L) = 0
      have hsecond : singularGenerator ℤ (TopCat.of B) 0
          ((TopCat.toSSet.obj (TopCat.of B)).δ (1 : Fin 2) s) ≫ L =
          v (ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint
            ((TopCat.toSSet.obj (TopCat.of B)).δ (1 : Fin 2) s)) := by
        simp [L,
          apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_chains,
          singularGenerator]
        erw [Limits.Sigma.ι_desc]
      rw [hsecond]
      rw [← sub_eq_add_neg]
      rw [sub_eq_zero]
      change v _ = v _
      apply hv_joined
      let τ₁ := ConstructionTargets.SingularSubdivision.continuousMapOfSingularSimplex 1 s
      have hs : ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
          (TopCat.of B) 1 τ₁ = s := by
        exact Equiv.symm_apply_apply _ s
      have hu (u w : stdSimplex ℝ (Fin 1)) : u = w := by
        ext i
        fin_cases i
        exact (stdSimplex.eq_one_of_unique u (0 : Fin 1)).trans
          (stdSimplex.eq_one_of_unique w (0 : Fin 1)).symm
      have h0 : ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint
          ((TopCat.toSSet.obj (TopCat.of B)).δ (0 : Fin 2) s) =
          τ₁ (ConstructionTargets.SingularSubdivision.standardSimplexVertices 1 1) := by
        rw [← hs, ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap_face
          (m := 0) τ₁ 0]
        simp only [ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint,
          ConstructionTargets.SingularSubdivision.continuousMapOfSingularSimplex_ofContinuousMap,
          ContinuousMap.comp_apply]
        change τ₁ (ConstructionTargets.SingularSubdivision.faceAffine 0 0
          (ConstructionTargets.SingularSubdivision.standardSimplexVertices 0 0)) = _
        exact congrArg τ₁ (congrFun
          (ConstructionTargets.SingularSubdivision.faceAffine_standardSimplexVertices 0 0) 0)
      have h1 : ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint
          ((TopCat.toSSet.obj (TopCat.of B)).δ (1 : Fin 2) s) =
          τ₁ (ConstructionTargets.SingularSubdivision.standardSimplexVertices 1 0) := by
        rw [← hs, ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap_face
          (m := 0) τ₁ 1]
        simp only [ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint,
          ConstructionTargets.SingularSubdivision.continuousMapOfSingularSimplex_ofContinuousMap,
          ContinuousMap.comp_apply]
        change τ₁ (ConstructionTargets.SingularSubdivision.faceAffine 0 1
          (ConstructionTargets.SingularSubdivision.standardSimplexVertices 0 0)) = _
        exact congrArg τ₁ (congrFun
          (ConstructionTargets.SingularSubdivision.faceAffine_standardSimplexVertices 0 1) 0)
      rw [h0, h1]
      exact ⟨(PathConnectedSpace.joined
        (ConstructionTargets.SingularSubdivision.standardSimplexVertices 1 1)
        (ConstructionTargets.SingularSubdivision.standardSimplexVertices 1 0)).somePath.map
          τ₁.continuous⟩
    let c : KB.cycles 0 ⟶ SingularHomology ℤ 0 (TopCat.of A) := KB.iCycles 0 ≫ L
    have hc : KB.toCycles 1 0 ≫ c = 0 := by
      dsimp [c]
      rw [← CategoryTheory.Category.assoc, HomologicalComplex.toCycles_i, hd]
    let g : SingularHomology ℤ 0 (TopCat.of B) ⟶ SingularHomology ℤ 0 (TopCat.of A) :=
      (KB.homologyIsCokernel 1 0 (by simp)).desc
        (CategoryTheory.Limits.CokernelCofork.ofπ c hc)
    have hπ : KB.homologyπ 0 ≫ g = c := by
      exact CategoryTheory.Limits.Cofork.IsColimit.π_desc
        (KB.homologyIsCokernel 1 0 (by simp))
    have hleft : HomologicalComplex.homologyMap (singularPostcomposition ℤ f) 0 ≫ g = 𝟙 _ := by
      apply (CategoryTheory.cancel_epi (zeroChainH0Class ℤ (X := A))).1
      apply Limits.Sigma.hom_ext
      intro s
      change singularGenerator ℤ (TopCat.of A) 0 s ≫
        zeroChainH0Class ℤ ≫ HomologicalComplex.homologyMap
          (singularPostcomposition ℤ f) 0 ≫ g =
        singularGenerator ℤ (TopCat.of A) 0 s ≫ zeroChainH0Class ℤ
      have hstep : singularGenerator ℤ (TopCat.of A) 0 s ≫
          zeroChainH0Class ℤ ≫ HomologicalComplex.homologyMap
            (singularPostcomposition ℤ f) 0 ≫ g =
          singularGenerator ℤ (TopCat.of A) 0 s ≫
            (singularPostcomposition ℤ f).f 0 ≫ zeroChainH0Class ℤ ≫ g := by
        simpa only [CategoryTheory.Category.assoc] using congrArg
          (fun q => singularGenerator ℤ (TopCat.of A) 0 s ≫ q ≫ g)
          (zeroChainH0Class_naturality ℤ f)
      rw [hstep]
      let τ := ConstructionTargets.SingularSubdivision.continuousMapOfSingularSimplex 0 s
      change singularGenerator ℤ (TopCat.of A) 0 s ≫
        (singularPostcomposition ℤ f).f 0 ≫ zeroChainH0Class ℤ ≫ g = _
      change singularGenerator ℤ (TopCat.of A) 0
        (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
          (TopCat.of A) 0 τ) ≫
        (singularPostcomposition ℤ f).f 0 ≫ zeroChainH0Class ℤ ≫ g = _
      have hgen : singularGenerator ℤ (TopCat.of A) 0
          (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
            (TopCat.of A) 0 τ) ≫ (singularPostcomposition ℤ f).f 0 =
          singularGenerator ℤ (TopCat.of B) 0
            (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
              (TopCat.of B) 0 (f.comp τ)) :=
        singularGenerator_singularPostcomposition ℤ 0 τ f
      have hstep2 := congrArg (fun q => q ≫ zeroChainH0Class ℤ ≫ g) hgen
      simp only [CategoryTheory.Category.assoc] at hstep2
      rw [hstep2]
      unfold zeroChainH0Class
      have hp := congrArg (fun q => singularGenerator ℤ (TopCat.of B) 0
        (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
          (TopCat.of B) 0 (f.comp τ)) ≫ zeroChainsToCycles ℤ ≫ q) hπ
      have hp' : (singularGenerator ℤ (TopCat.of B) 0
          (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
            (TopCat.of B) 0 (f.comp τ)) ≫ zeroChainsToCycles ℤ ≫
            KB.homologyπ 0) ≫ g =
          (singularGenerator ℤ (TopCat.of B) 0
            (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
              (TopCat.of B) 0 (f.comp τ)) ≫ zeroChainsToCycles ℤ) ≫ c := by
        simpa only [CategoryTheory.Category.assoc] using hp
      rw [← CategoryTheory.Category.assoc]
      change (singularGenerator ℤ (TopCat.of B) 0
          (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
            (TopCat.of B) 0 (f.comp τ)) ≫ zeroChainsToCycles ℤ ≫
            KB.homologyπ 0) ≫ g = _
      rw [hp']
      dsimp [c]
      have hz := congrArg (fun q => singularGenerator ℤ (TopCat.of B) 0
        (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
          (TopCat.of B) 0 (f.comp τ)) ≫ q ≫ L)
        (zeroChainsToCycles_i ℤ (X := B))
      have hz' : ((singularGenerator ℤ (TopCat.of B) 0
          (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
            (TopCat.of B) 0 (f.comp τ)) ≫ zeroChainsToCycles ℤ) ≫
            KB.iCycles 0) ≫ L =
          singularGenerator ℤ (TopCat.of B) 0
            (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
              (TopCat.of B) 0 (f.comp τ)) ≫ L := by
        simpa only [CategoryTheory.Category.assoc, CategoryTheory.Category.id_comp] using hz
      rw [← CategoryTheory.Category.assoc]
      rw [hz']
      change singularGenerator ℤ (TopCat.of B) 0
          (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
            (TopCat.of B) 0 (f.comp τ)) ≫ L =
        singularGenerator ℤ (TopCat.of A) 0 s ≫ zeroChainH0Class ℤ
      rw [singularGenerator_zeroChainH0Class ℤ]
      simp [L,
        apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_chains,
        singularGenerator]
      erw [Limits.Sigma.ι_desc]
      change v (f (ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint s)) = _
      dsimp [v, apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_vertex,
        apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined_aux_pick]
      have hex : ∃ a : A, Joined (f a)
          (f (ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint s)) :=
        ⟨_, Joined.refl _⟩
      rw [dif_pos hex]
      apply singularVertexH0Class_eq_of_path ℤ
      apply (hf _ _ ?_).somePath
      exact Classical.choose_spec hex
    intro x y hxy
    have := congrArg (fun z => g.hom z) hxy
    have hx := congrArg (fun q : SingularHomology ℤ 0 (TopCat.of A) ⟶
      SingularHomology ℤ 0 (TopCat.of A) => q x) hleft
    have hy := congrArg (fun q : SingularHomology ℤ 0 (TopCat.of A) ⟶
      SingularHomology ℤ 0 (TopCat.of A) => q y) hleft
    exact hx.symm.trans (this.trans hy)

/-- The inclusion `U ∩ V → U` reflects path-joinedness: points joined in
`U ≅ PT ⊔ PT` lie in the same summand, and there in the same punctured square
`N`, which is path connected
(`apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_N_pathConnected`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_incl_joined
    (x y : ↥(apm_t01a03_separating_circle_H1_zero_aux_U ∩
      apm_t01a03_separating_circle_H1_zero_aux_V)) :
    Joined (Set.inclusion Set.inter_subset_left x : ↥apm_t01a03_separating_circle_H1_zero_aux_U)
      (Set.inclusion Set.inter_subset_left y) → Joined x y := by
  rintro hxy
  rcases x with ⟨x, hxU, hxV⟩
  rcases y with ⟨y, hyU, hyV⟩
  rcases hxU with ⟨a, rfl⟩
  rcases hyU with ⟨b, rfl⟩
  let e : apm_t01a03_TwoPuncturedTori ≃ₜ
      apm_t01a03_separating_circle_H1_zero_aux_U :=
    OnePoint.isOpenEmbedding_coe.toHomeomorph
  have hab : Joined a b := by
    have hp : Joined (e.symm (Set.inclusion Set.inter_subset_left
          ⟨↑a, ⟨⟨a, rfl⟩, hxV⟩⟩))
        (e.symm (Set.inclusion Set.inter_subset_left
          ⟨↑b, ⟨⟨b, rfl⟩, hyV⟩⟩)) :=
      ⟨hxy.somePath.map e.symm.continuous⟩
    have hea : e.symm (Set.inclusion Set.inter_subset_left
        ⟨↑a, ⟨⟨a, rfl⟩, hxV⟩⟩) = a := by
      exact OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph_symm_apply a
    have heb : e.symm (Set.inclusion Set.inter_subset_left
        ⟨↑b, ⟨⟨b, rfl⟩, hyV⟩⟩) = b := by
      exact OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph_symm_apply b
    rwa [hea, heb] at hp
  have haN : a ∈ apm_t01a03_separating_circle_H1_zero_aux_Nsum := by
    simpa [apm_t01a03_separating_circle_H1_zero_aux_V] using hxV
  have hbN : b ∈ apm_t01a03_separating_circle_H1_zero_aux_Nsum := by
    simpa [apm_t01a03_separating_circle_H1_zero_aux_V] using hyV
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have ha : a ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using haN
          have hb : b ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hbN
          let f : apm_t01a03_separating_circle_H1_zero_aux_N →
              ↥(apm_t01a03_separating_circle_H1_zero_aux_U ∩
                apm_t01a03_separating_circle_H1_zero_aux_V) := fun z =>
            ⟨(↑(Sum.inl z.1 : apm_t01a03_TwoPuncturedTori) :
                OnePoint apm_t01a03_TwoPuncturedTori),
              ⟨by
                show ↑(Sum.inl z.1 : apm_t01a03_TwoPuncturedTori) ∈
                  apm_t01a03_separating_circle_H1_zero_aux_U
                exact ⟨Sum.inl z.1, rfl⟩, by
                change ↑(Sum.inl z.1 : apm_t01a03_TwoPuncturedTori) ∉
                  ((↑) : apm_t01a03_TwoPuncturedTori →
                    OnePoint apm_t01a03_TwoPuncturedTori) ''
                    apm_t01a03_separating_circle_H1_zero_aux_Nsumᶜ
                rintro ⟨q, hq, heq⟩
                have hqa : q = Sum.inl z.1 := OnePoint.coe_injective heq
                subst q
                exact hq (by simp [apm_t01a03_separating_circle_H1_zero_aux_Nsum,
                  z.2])⟩⟩
          have hf : Continuous f :=
            Continuous.subtype_mk
              (OnePoint.continuous_coe.comp
                (continuous_inl.comp continuous_subtype_val)) _
          letI : PathConnectedSpace
              apm_t01a03_separating_circle_H1_zero_aux_N :=
            apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_N_pathConnected
          exact ⟨(PathConnectedSpace.somePath ⟨a, ha⟩ ⟨b, hb⟩).map hf⟩
      | inr b =>
          have hs : Sum.inl a ∈ Set.range hab.somePath :=
            ⟨0, hab.somePath.source⟩
          have hi : Sum.inl a ∈ Set.range
              (Sum.inl : apm_t01a03_PuncturedTorus →
                apm_t01a03_TwoPuncturedTori) := ⟨a, rfl⟩
          have hr := (isPreconnected_range hab.somePath.continuous).subset_isClopen
            isClopen_range_inl ⟨_, hs, hi⟩
          rcases hr ⟨1, hab.somePath.target⟩ with ⟨c, hc⟩
          exact False.elim (Sum.inl_ne_inr hc)
  | inr a =>
      cases b with
      | inl b =>
          have hs : Sum.inr a ∈ Set.range hab.somePath :=
            ⟨0, hab.somePath.source⟩
          have hi : Sum.inr a ∈ Set.range
              (Sum.inr : apm_t01a03_PuncturedTorus →
                apm_t01a03_TwoPuncturedTori) := ⟨a, rfl⟩
          have hr := (isPreconnected_range hab.somePath.continuous).subset_isClopen
            isClopen_range_inr ⟨_, hs, hi⟩
          rcases hr ⟨1, hab.somePath.target⟩ with ⟨c, hc⟩
          exact False.elim (Sum.inr_ne_inl hc)
      | inr b =>
          have ha : a ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using haN
          have hb : b ∈ apm_t01a03_separating_circle_H1_zero_aux_N := by
            simpa [apm_t01a03_separating_circle_H1_zero_aux_Nsum] using hbN
          let f : apm_t01a03_separating_circle_H1_zero_aux_N →
              ↥(apm_t01a03_separating_circle_H1_zero_aux_U ∩
                apm_t01a03_separating_circle_H1_zero_aux_V) := fun z =>
            ⟨(↑(Sum.inr z.1 : apm_t01a03_TwoPuncturedTori) :
                OnePoint apm_t01a03_TwoPuncturedTori),
              ⟨by
                show ↑(Sum.inr z.1 : apm_t01a03_TwoPuncturedTori) ∈
                  apm_t01a03_separating_circle_H1_zero_aux_U
                exact ⟨Sum.inr z.1, rfl⟩, by
                change ↑(Sum.inr z.1 : apm_t01a03_TwoPuncturedTori) ∉
                  ((↑) : apm_t01a03_TwoPuncturedTori →
                    OnePoint apm_t01a03_TwoPuncturedTori) ''
                    apm_t01a03_separating_circle_H1_zero_aux_Nsumᶜ
                rintro ⟨q, hq, heq⟩
                have hqa : q = Sum.inr z.1 := OnePoint.coe_injective heq
                subst q
                exact hq (by simp [apm_t01a03_separating_circle_H1_zero_aux_Nsum,
                  z.2])⟩⟩
          have hf : Continuous f :=
            Continuous.subtype_mk
              (OnePoint.continuous_coe.comp
                (continuous_inr.comp continuous_subtype_val)) _
          letI : PathConnectedSpace
              apm_t01a03_separating_circle_H1_zero_aux_N :=
            apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_N_pathConnected
          exact ⟨(PathConnectedSpace.somePath ⟨a, ha⟩ ⟨b, hb⟩).map hf⟩

/-- `H₀ (U ∩ V) → H₀ U` is injective: `U ∩ V` is the two punctured squares, each
path connected, landing in different summands of `U ≅ PT ⊔ PT`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj :
    Function.Injective (IntegralMV.mvIncl
      (Set.inter_subset_left : apm_t01a03_separating_circle_H1_zero_aux_U ∩
        apm_t01a03_separating_circle_H1_zero_aux_V ⊆
          apm_t01a03_separating_circle_H1_zero_aux_U) 0).hom :=
  apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined _
    apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_incl_joined

/-- Bridge: `coe : PT ⊔ PT → U` is a homeomorphism, and `IntegralMV.HZ 1` is
`apm_t01a03_H1`, so a surjection `H₁ U → H₁ X` gives one from `H₁ (PT ⊔ PT)`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_U_bridge
    (h : Function.Surjective
      (IntegralMV.mvToX apm_t01a03_separating_circle_H1_zero_aux_U 1).hom) :
    Function.Surjective (apm_t01a03_H1map
      (⟨(↑), OnePoint.continuous_coe⟩ :
        C(apm_t01a03_TwoPuncturedTori, OnePoint apm_t01a03_TwoPuncturedTori))) := by
  let e : apm_t01a03_TwoPuncturedTori ≃ₜ
      apm_t01a03_separating_circle_H1_zero_aux_U :=
    OnePoint.isOpenEmbedding_coe.toHomeomorph
  let ec : C(apm_t01a03_TwoPuncturedTori,
      apm_t01a03_separating_circle_H1_zero_aux_U) := ⟨e, e.continuous⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  letI : IsIso (TopCat.ofHom ec) := by
    change IsIso (TopCat.isoOfHomeo
      (X := TopCat.of apm_t01a03_TwoPuncturedTori)
      (Y := TopCat.of apm_t01a03_separating_circle_H1_zero_aux_U) e).hom
    infer_instance
  have hepi : Epi (F.map (TopCat.ofHom ec)) := by infer_instance
  have he : Function.Surjective (F.map (TopCat.ofHom ec)) :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  intro y
  obtain ⟨u, hu⟩ := h y
  obtain ⟨x, hx⟩ := he u
  refine ⟨x, ?_⟩
  have hcomp :
      (⟨(↑), OnePoint.continuous_coe⟩ :
        C(apm_t01a03_TwoPuncturedTori,
          OnePoint apm_t01a03_TwoPuncturedTori)) =
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(apm_t01a03_separating_circle_H1_zero_aux_U,
            OnePoint apm_t01a03_TwoPuncturedTori)).comp ec := by
    ext z
    rfl
  change F.map (TopCat.ofHom ⟨(↑), OnePoint.continuous_coe⟩) x = y
  rw [hcomp]
  rw [show F.map (TopCat.ofHom ((⟨Subtype.val, continuous_subtype_val⟩ :
      C(apm_t01a03_separating_circle_H1_zero_aux_U,
        OnePoint apm_t01a03_TwoPuncturedTori)).comp ec)) =
      F.map (TopCat.ofHom ec) ≫
        IntegralMV.mvToX apm_t01a03_separating_circle_H1_zero_aux_U 1 by
      change _ = F.map (TopCat.ofHom ec) ≫
        F.map (TopCat.ofHom
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(apm_t01a03_separating_circle_H1_zero_aux_U,
              OnePoint apm_t01a03_TwoPuncturedTori)))
      rw [← F.map_comp]
      rfl]
  simpa only [CategoryTheory.comp_apply, hx] using hu

/-- The model: `H₁` of the one-point compactification is reached from the
two punctured tori. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_model_surj :
    Function.Surjective (apm_t01a03_H1map
      (⟨(↑), OnePoint.continuous_coe⟩ :
        C(apm_t01a03_TwoPuncturedTori, OnePoint apm_t01a03_TwoPuncturedTori))) := by
  set U := apm_t01a03_separating_circle_H1_zero_aux_U
  set V := apm_t01a03_separating_circle_H1_zero_aux_V
  have hU : IsOpen U := OnePoint.isOpen_range_coe
  have hcov : U ∪ V = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    induction p using OnePoint.rec with
    | infty =>
      right
      rintro ⟨y, -, hy⟩
      exact OnePoint.coe_ne_infty y hy
    | coe y => exact Or.inl ⟨y, rfl⟩
  obtain ⟨δ, -, h2, h3⟩ := IntegralMV.integralMayerVietoris U V hU
    apm_t01a03_separating_circle_H1_zero_aux_V_open hcov
  have hI : Function.Injective (IntegralMV.mvI U V 0).hom := by
    intro a b hab
    apply apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj
    have := congrArg (Limits.biprod.fst :
      IntegralMV.HZ 0 U ⊞ IntegralMV.HZ 0 V ⟶ _).hom hab
    simpa [IntegralMV.mvI, ← ModuleCat.comp_apply] using this
  have hδ : (δ 0).hom = 0 := by
    rw [← LinearMap.range_eq_bot, h3 0]
    exact LinearMap.ker_eq_bot.mpr hI
  have hJ : Function.Surjective (IntegralMV.mvJ U V 1).hom := by
    rw [← LinearMap.range_eq_top]
    have := h2 0
    rw [hδ, LinearMap.ker_zero] at this
    exact this
  apply apm_t01a03_separating_circle_H1_zero_aux_U_bridge
  have hVz := apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero
  have hJ' : IntegralMV.mvJ U V 1 = CategoryStruct.comp
      (Limits.biprod.fst : IntegralMV.HZ 1 U ⊞ IntegralMV.HZ 1 V ⟶ _)
      (IntegralMV.mvToX U 1) := by
    apply Limits.biprod.hom_ext'
    · simp [IntegralMV.mvJ]
    · simp only [IntegralMV.mvJ, Limits.biprod.inr_desc, Limits.biprod.inr_fst_assoc,
        Limits.zero_comp]
      rw [hVz.eq_of_src (IntegralMV.mvToX V 1) 0, neg_zero]
  intro y
  obtain ⟨z, rfl⟩ := hJ y
  exact ⟨(Limits.biprod.fst : IntegralMV.HZ 1 U ⊞ IntegralMV.HZ 1 V ⟶ _).hom z, by
    rw [hJ']; rfl⟩

/-! #### `_aux_model_free` by two side retractions

`X = OnePoint (PT ⊔ PT)` is two tori `OnePoint PT` wedged at `∞`. Each side
includes (`OnePoint.map Sum.inl`) and retracts (collapse the other side to `∞`).
The retractions split the inclusions on `H₁`, so `H₁ T × H₁ T → H₁ X` is
injective; it is onto because `H₁ (PT ⊔ PT)` is spanned by the two summands
and reaches all of `H₁ X` (`_aux_model_surj`). No homotopy is needed. -/

/-- Collapse the right-hand torus to `∞`. -/
def apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_rL :
    OnePoint apm_t01a03_TwoPuncturedTori → OnePoint apm_t01a03_PuncturedTorus :=
  fun p => p.elim OnePoint.infty (Sum.elim (↑) (fun _ => OnePoint.infty))

/-- Collapse the left-hand torus to `∞`. -/
def apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_rR :
    OnePoint apm_t01a03_TwoPuncturedTori → OnePoint apm_t01a03_PuncturedTorus :=
  fun p => p.elim OnePoint.infty (Sum.elim (fun _ => OnePoint.infty) (↑))

/-- The two side inclusions are continuous: `Sum.inl`, `Sum.inr` are closed
embeddings, so they tend to the cocompact filter (`OnePoint.continuous_map_iff`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_incl_continuous :
    Continuous (OnePoint.map (Sum.inl : apm_t01a03_PuncturedTorus →
        apm_t01a03_TwoPuncturedTori)) ∧
      Continuous (OnePoint.map (Sum.inr : apm_t01a03_PuncturedTorus →
        apm_t01a03_TwoPuncturedTori)) := by
  sorry

/-- The two collapses are continuous: the preimage of a neighbourhood of `∞`
contains `∞`, the whole collapsed side, and a cocompact part of the kept side. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_retr_continuous :
    Continuous apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_rL ∧
      Continuous apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_rR := by
  sorry

/-- `OnePoint PT` is the torus (`OnePoint.equivOfIsEmbeddingOfRangeEq`), whose
`H₁` is `ℤ²` (`BoundaryTorusH0Cokernel.boundaryTorus_complete_module_homology`,
after `Circle ≃ₜ BoundaryCircle`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_torus :
    Nonempty (apm_t01a03_H1 (OnePoint apm_t01a03_PuncturedTorus) ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) := by
  sorry

/-- `H₁` of a topological sum is spanned by the two summands
(`TopologicalSumSingularHomology.sumHomologyIsoBiprod`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_sum_span
    (w : apm_t01a03_H1 apm_t01a03_TwoPuncturedTori) :
    ∃ a b : apm_t01a03_H1 apm_t01a03_PuncturedTorus,
      w = apm_t01a03_H1map (⟨Sum.inl, continuous_inl⟩ :
          C(apm_t01a03_PuncturedTorus, apm_t01a03_TwoPuncturedTori)) a +
        apm_t01a03_H1map (⟨Sum.inr, continuous_inr⟩ :
          C(apm_t01a03_PuncturedTorus, apm_t01a03_TwoPuncturedTori)) b := by
  sorry

lemma apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : apm_t01a03_H1 X) :
    apm_t01a03_H1map g (apm_t01a03_H1map f x) = apm_t01a03_H1map (g.comp f) x := by
  change (apm_t01a03_H1map f ≫ apm_t01a03_H1map g) x = _
  rw [apm_t01a03_H1map, apm_t01a03_H1map, apm_t01a03_H1map, ← Functor.map_comp]
  rfl

lemma apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_id_apply
    {X : Type} [TopologicalSpace X] (f : C(X, X)) (hf : ∀ x, f x = x)
    (x : apm_t01a03_H1 X) : apm_t01a03_H1map f x = x := by
  have : f = ContinuousMap.id X := by ext y; exact hf y
  subst this
  change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (𝟙 (TopCat.of X)) x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The model: the one-point compactification of two punctured tori (a wedge
of two tori) has `H₁ ≅ ℤ⁴`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_model_free :
    Nonempty (apm_t01a03_H1 (OnePoint apm_t01a03_TwoPuncturedTori) ≅
      ModuleCat.of ℤ (Fin 4 → ℤ)) := by
  obtain ⟨hiL, hiR⟩ :=
    apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_incl_continuous
  obtain ⟨hrL, hrR⟩ :=
    apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_retr_continuous
  obtain ⟨eT⟩ := apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_torus
  let iL : C(OnePoint apm_t01a03_PuncturedTorus,
      OnePoint apm_t01a03_TwoPuncturedTori) := ⟨_, hiL⟩
  let iR : C(OnePoint apm_t01a03_PuncturedTorus,
      OnePoint apm_t01a03_TwoPuncturedTori) := ⟨_, hiR⟩
  let rL : C(OnePoint apm_t01a03_TwoPuncturedTori,
      OnePoint apm_t01a03_PuncturedTorus) := ⟨_, hrL⟩
  let rR : C(OnePoint apm_t01a03_TwoPuncturedTori,
      OnePoint apm_t01a03_PuncturedTorus) := ⟨_, hrR⟩
  let Φ := (apm_t01a03_H1map iL).hom.coprod (apm_t01a03_H1map iR).hom
  have hcomp := @apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_comp_apply
  have hid := @apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_id_apply
  have hconst := @apm_t01a03_separating_circle_H1_zero_aux_const
  -- the retractions split the inclusions
  have hLL : ∀ x, apm_t01a03_H1map rL (apm_t01a03_H1map iL x) = x := fun x => by
    rw [hcomp]; exact hid _ (fun p => by induction p using OnePoint.rec <;> rfl) x
  have hRR : ∀ x, apm_t01a03_H1map rR (apm_t01a03_H1map iR x) = x := fun x => by
    rw [hcomp]; exact hid _ (fun p => by induction p using OnePoint.rec <;> rfl) x
  have hLR : ∀ x, apm_t01a03_H1map rL (apm_t01a03_H1map iR x) = 0 := fun x => by
    rw [hcomp, hconst (rL.comp iR) OnePoint.infty
      (fun p => by induction p using OnePoint.rec <;> rfl)]
    rfl
  have hRL : ∀ x, apm_t01a03_H1map rR (apm_t01a03_H1map iL x) = 0 := fun x => by
    rw [hcomp, hconst (rR.comp iL) OnePoint.infty
      (fun p => by induction p using OnePoint.rec <;> rfl)]
    rfl
  have hinj : Function.Injective Φ := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Φ, LinearMap.coprod_apply] at h
    have h1 := congrArg (apm_t01a03_H1map rL) h
    have h2 := congrArg (apm_t01a03_H1map rR) h
    simp only [map_add, hLL, hRR, hLR, hRL, add_zero, zero_add] at h1 h2
    exact Prod.ext h1 h2
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨w, rfl⟩ := apm_t01a03_separating_circle_H1_zero_aux_model_surj y
    obtain ⟨a, b, rfl⟩ :=
      apm_t01a03_separating_circle_H1_zero_aux_model_free_aux_sum_span w
    refine ⟨(apm_t01a03_H1map (⟨(↑), OnePoint.continuous_coe⟩ :
        C(apm_t01a03_PuncturedTorus, OnePoint apm_t01a03_PuncturedTorus)) a,
      apm_t01a03_H1map (⟨(↑), OnePoint.continuous_coe⟩ :
        C(apm_t01a03_PuncturedTorus, OnePoint apm_t01a03_PuncturedTorus)) b), ?_⟩
    simp only [Φ, LinearMap.coprod_apply, map_add]
    rw [hcomp, hcomp, hcomp, hcomp]
    rfl
  let eΦ := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let e2 := eT.toLinearEquiv
  let e4 : ((Fin 2 → ℤ) × (Fin 2 → ℤ)) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) ℤ ℤ).symm ≪≫ₗ
      LinearEquiv.funCongrLeft ℤ ℤ (finSumFinEquiv (m := 2) (n := 2)).symm
  exact ⟨(eΦ.symm ≪≫ₗ e2.prodCongr e2 ≪≫ₗ e4).toModuleIso⟩

lemma apm_t01a03_separating_circle_H1_zero_aux_homeo_surj
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Function.Surjective (apm_t01a03_H1map (e : C(X, Y))) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hfun : apm_t01a03_H1map (e.symm : C(Y, X)) ≫ apm_t01a03_H1map (e : C(X, Y)) =
      𝟙 (apm_t01a03_H1 Y) := by
    change CategoryStruct.comp (F.map (TopCat.ofHom _)) (F.map (TopCat.ofHom _)) = 𝟙 _
    rw [← F.map_comp]
    change F.map (TopCat.ofHom ((e : C(X, Y)).comp (e.symm : C(Y, X)))) = 𝟙 _
    have : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
      ext y
      simp
    rw [this]
    exact F.map_id (TopCat.of Y)
  intro y
  refine ⟨apm_t01a03_H1map (e.symm : C(Y, X)) y, ?_⟩
  have := congrArg (fun q : apm_t01a03_H1 Y ⟶ apm_t01a03_H1 Y ↦ q y) hfun
  simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using this

/-- **Assembly (sorry-free given the five leaves above).** An embedded circle
whose complement is two punctured tori represents zero in integral `H₁`. -/
theorem apm_t01a03_separating_circle_H1_zero
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t01a03_E2 S]
    [IsManifold apm_t01a03_I2 ∞ S]
    (hgenus : apm_t01a03_hasGenusTwo S)
    (middle : C(Circle, S))
    (hmiddle : apm_t01a03_IsMiddleCircle middle) :
    apm_t01a03_H1map middle = 0 := by
  obtain ⟨_hemb, ⟨e⟩⟩ := hmiddle
  obtain ⟨ρ, hρC, hρU⟩ :=
    apm_t01a03_separating_circle_H1_zero_aux_collapse middle e
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  let j : C({x : S // x ∉ Set.range middle}, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let ι : C(apm_t01a03_TwoPuncturedTori, OnePoint apm_t01a03_TwoPuncturedTori) :=
    ⟨(↑), OnePoint.continuous_coe⟩
  have hcomm : ρ.comp j = ι.comp (e : C(_, apm_t01a03_TwoPuncturedTori)) := by
    ext x
    exact hρU x
  have hfun : CategoryStruct.comp (apm_t01a03_H1map j) (apm_t01a03_H1map ρ) =
      CategoryStruct.comp (apm_t01a03_H1map (e : C(_, apm_t01a03_TwoPuncturedTori)))
        (apm_t01a03_H1map ι) := by
    change CategoryStruct.comp (F.map (TopCat.ofHom _)) (F.map (TopCat.ofHom _)) =
      CategoryStruct.comp (F.map (TopCat.ofHom _)) (F.map (TopCat.ofHom _))
    rw [← F.map_comp, ← F.map_comp]
    change F.map (TopCat.ofHom (ρ.comp j)) =
      F.map (TopCat.ofHom (ι.comp (e : C(_, apm_t01a03_TwoPuncturedTori))))
    rw [hcomm]
  have hsurj : Function.Surjective (apm_t01a03_H1map ρ) := by
    intro y
    obtain ⟨u, rfl⟩ := apm_t01a03_separating_circle_H1_zero_aux_model_surj y
    obtain ⟨v, rfl⟩ := apm_t01a03_separating_circle_H1_zero_aux_homeo_surj e u
    refine ⟨apm_t01a03_H1map j v, ?_⟩
    have := congrArg (fun q ↦ q v) hfun
    simpa only [CategoryTheory.comp_apply] using this
  have hinj := apm_t01a03_separating_circle_H1_zero_aux_hopf
    hgenus.2.1.some apm_t01a03_separating_circle_H1_zero_aux_model_free.some _ hsurj
  have hzero : apm_t01a03_H1map middle ≫ apm_t01a03_H1map ρ = 0 := by
    change CategoryStruct.comp (F.map (TopCat.ofHom _)) (F.map (TopCat.ofHom _)) = 0
    rw [← F.map_comp]
    exact apm_t01a03_separating_circle_H1_zero_aux_const (ρ.comp middle)
      OnePoint.infty hρC
  ext x
  apply hinj
  have := congrArg (fun q ↦ q x) hzero
  simpa only [CategoryTheory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
    map_zero] using this

theorem apm_t01a03 :
    ∀ (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
      [PathConnectedSpace S] [ChartedSpace apm_t01a03_E2 S]
      [IsManifold apm_t01a03_I2 ∞ S],
      apm_t01a03_hasGenusTwo S →
      ∀ (middle : C(Circle, S))
        (wedgeInTorus : C(apm_t01a03_Wedge, apm_t01a03_Torus))
        (twoCircles : C(apm_t01a03_TwoCircles, S)),
        apm_t01a03_IsMiddleCircle middle →
        apm_t01a03_IsTypicalWedge wedgeInTorus →
        apm_t01a03_IsSeparatingTwoCircles twoCircles →
        ¬apm_t01a03_HasRetraction middle ∧
        ¬apm_t01a03_HasRetraction wedgeInTorus ∧
        ¬apm_t01a03_HasRetraction twoCircles := by
  intro S _ _ _ _ _ _ hgenus middle wedgeInTorus twoCircles
    hmiddle hwedge _htwo
  have hmiddleH1 :=
    apm_t01a03_separating_circle_H1_zero hgenus middle hmiddle
  have hwedgePi :=
    apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective
      apm_t01a03_circleWedge_pi1_noncommutative wedgeInTorus hwedge
  refine ⟨apm_t01a03_noRetraction_circle_of_H1_nontrivial middle hmiddleH1,
    ?_, apm_t01a03_noRetraction_twoCircles twoCircles⟩
  intro hret
  exact hwedgePi
    (apm_t01a03_fundamentalGroupMap_injective_of_retraction
      wedgeInTorus apm_t01a03_wedgeBase hret)

#print axioms apm_t01a03
