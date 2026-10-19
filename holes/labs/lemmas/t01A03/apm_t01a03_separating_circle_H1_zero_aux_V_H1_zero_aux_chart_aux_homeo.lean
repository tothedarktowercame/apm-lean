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

/-- The model: the one-point compactification of two punctured tori (a wedge
of two tori) has `H₁ ≅ ℤ⁴`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_model_free :
    Nonempty (apm_t01a03_H1 (OnePoint apm_t01a03_TwoPuncturedTori) ≅
      ModuleCat.of ℤ (Fin 4 → ℤ)) := by
  sorry

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
-- BEGIN SEAT AREA
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_homeo :
    ∃ φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
        (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)),
      ∀ x, (φ x : Fin 2 → ℝ) =
        apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x.1 := by
  sorry
-- END SEAT AREA

/-- Away from the puncture the points of `N` lie in a compact set: for `ε > 0`,
take the image of the compact `{θ | ε ≤ ‖θ‖ ≤ 1}` under
`θ ↦ (Circle.exp (π/3·θ₀), Circle.exp (π/3·θ₁))` (it avoids `(1,1)` since
`0 < ‖θ‖ ≤ 1`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_far :
    ∀ ε > 0, ∃ C : Set apm_t01a03_PuncturedTorus, IsCompact C ∧
      ∀ x ∈ apm_t01a03_separating_circle_H1_zero_aux_N,
        ε ≤ ‖apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x‖ →
          x ∈ C := by
  sorry

/-- A compact subset of the punctured torus misses a neighbourhood of the puncture:
its image in the torus is compact, hence closed, and omits `(1,1)`; small angles
put a point close to `(1,1)`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_near :
    ∀ C : Set apm_t01a03_PuncturedTorus, IsCompact C → ∃ r > 0,
      ∀ x ∈ apm_t01a03_separating_circle_H1_zero_aux_N,
        ‖apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_chart_aux_angle x‖ < r →
          x ∉ C := by
  sorry

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
  sorry

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
  sorry

/-- The glued map is open. An open set of `V` away from `∞` is open in a
summand, and `φ` carries it onto an open subset of a punctured square, which is
open in `W`. An open set of `V` containing `∞` contains `V` minus the image of a
compact `C ⊔ C'` of `PT ⊔ PT`; by `hnear` (applied to each part) there is
`r > 0` with every point of `W` of norm `< r` in the image, so the image is a
neighbourhood of `(0, 0)`. -/
lemma apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_isOpenMap
    (φ : apm_t01a03_separating_circle_H1_zero_aux_N ≃ₜ
      (Metric.ball (0 : Fin 2 → ℝ) 1 \ {0} : Set (Fin 2 → ℝ)))
    (hnear : ∀ C : Set apm_t01a03_PuncturedTorus, IsCompact C → ∃ r > 0,
          ∀ x, ‖(φ x : Fin 2 → ℝ)‖ < r → (x : apm_t01a03_PuncturedTorus) ∉ C) :
    IsOpenMap (apm_t01a03_separating_circle_H1_zero_aux_V_H1_zero_aux_homeomorph_aux_forward φ) := by
  sorry

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
  sorry

/-- A map that reflects path-joinedness is injective on integral `H₀`.
(`H₀ A` is free on the path components of `A`; one route: for each path
component `K` of the target, counting the vertices of a `0`-chain that lie in `K`
kills boundaries, and these counts separate the vertex classes
`CoefficientH0.singularVertexH0Class` of distinct source components.) -/
lemma apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_H0_inj_of_joined
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B))
    (hf : ∀ a a' : A, Joined (f a) (f a') → Joined a a') :
    Function.Injective (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ f) 0).hom := by
  sorry

/-- The inclusion `U ∩ V → U` reflects path-joinedness: points joined in
`U ≅ PT ⊔ PT` lie in the same summand, and there in the same punctured square
`N`, which is path connected
(`apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_N_pathConnected`). -/
lemma apm_t01a03_separating_circle_H1_zero_aux_inter_H0_inj_aux_incl_joined
    (x y : ↥(apm_t01a03_separating_circle_H1_zero_aux_U ∩
      apm_t01a03_separating_circle_H1_zero_aux_V)) :
    Joined (Set.inclusion Set.inter_subset_left x : ↥apm_t01a03_separating_circle_H1_zero_aux_U)
      (Set.inclusion Set.inter_subset_left y) → Joined x y := by
  sorry

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
