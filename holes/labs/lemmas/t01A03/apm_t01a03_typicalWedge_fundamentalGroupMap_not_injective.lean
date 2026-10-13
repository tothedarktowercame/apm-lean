import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.CircleSingularHomology
import ConstructionTargets.Surfaces
import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.PointWedgeVanKampen

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

/-- **LIBRARY (point-wedge van Kampen).** The concrete wedge has two
noncommuting based loop classes. -/
theorem apm_t01a03_circleWedge_pi1_noncommutative :
    ∃ a b : FundamentalGroup apm_t01a03_Wedge apm_t01a03_wedgeBase,
      a * b ≠ b * a := by
  sorry

/-- The torus target has abelian fundamental group, so any map from a wedge
with two noncommuting loops is noninjective. The source fact is an explicit
hypothesis so this lemma is independently assignable. -/
-- BEGIN SEAT AREA
theorem apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective
    (hsource : ∃ a b : FundamentalGroup apm_t01a03_Wedge apm_t01a03_wedgeBase,
      a * b ≠ b * a)
    (wedge : C(apm_t01a03_Wedge, apm_t01a03_Torus))
    (_hwedge : apm_t01a03_IsTypicalWedge wedge) :
    ¬Function.Injective
      (FundamentalGroup.map wedge apm_t01a03_wedgeBase) := by
  sorry
-- END SEAT AREA

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
