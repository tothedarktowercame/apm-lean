import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.CircleSingularHomology
import ConstructionTargets.Surfaces
import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.PolygonCellPiOne

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

/-- **LIBRARY (surface-curve collar / fundamental class).** An embedded circle
whose complement is two punctured tori represents zero in integral `H₁`. -/
theorem apm_t01a03_separating_circle_H1_zero
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t01a03_E2 S]
    [IsManifold apm_t01a03_I2 ∞ S]
    (hgenus : apm_t01a03_hasGenusTwo S)
    (middle : C(Circle, S))
    (hmiddle : apm_t01a03_IsMiddleCircle middle) :
    apm_t01a03_H1map middle = 0 := by
  sorry

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
