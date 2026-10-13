import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.CircleSingularHomology
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.SurfaceSchoenflies

/-! # Blueprint for the repaired APM t03J01 statement -/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t03j01_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t03j01_Model := modelWithCornersSelf ℝ apm_t03j01_E2

abbrev apm_t03j01_H1 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

abbrev apm_t03j01_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t03j01_HasGenusTwoHomology
    (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty (apm_t03j01_H 0 X ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t03j01_H 1 X ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
  Nonempty (apm_t03j01_H 2 X ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t03j01_H k X)

def apm_t03j01_IsCurve
    {X : Type*} [TopologicalSpace X] (J : Set X) : Prop :=
  Nonempty (Circle ≃ₜ J)

def apm_t03j01_inclusion {X : Type} [TopologicalSpace X] (J : Set X) : C(J, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def apm_t03j01_H1Map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

def apm_t03j01_CutsIntoTwicePuncturedTorus
    {X : Type} [TopologicalSpace X] (J : Set X) : Prop :=
  IsConnected (Jᶜ)

def apm_t03j01_CutsIntoTwoOncePuncturedTori
    {X : Type} [TopologicalSpace X] (J : Set X) : Prop :=
  ¬IsConnected (Jᶜ)

def apm_t03j01_RetractsOnto
    {X : Type*} [TopologicalSpace X] (J : Set X) : Prop :=
  ∃ r : C(X, J), ∀ y : J, r y = y

lemma apm_t03j01_retraction_comp_inclusion_eq_id
    {X : Type} [TopologicalSpace X] {J : Set X}
    (h : apm_t03j01_RetractsOnto J) :
    (h.choose.comp (apm_t03j01_inclusion J)) = ContinuousMap.id J := by
  ext y
  exact congr_arg Subtype.val (h.choose_spec y)

lemma apm_t03j01_H1Map_injective_of_retraction
    {X : Type} [TopologicalSpace X] {J : Set X}
    (h : apm_t03j01_RetractsOnto J) :
    Function.Injective (apm_t03j01_H1Map (apm_t03j01_inclusion J)) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hcomp :
      apm_t03j01_H1Map (apm_t03j01_inclusion J) ≫
          apm_t03j01_H1Map h.choose = 𝟙 (apm_t03j01_H1 J) := by
    change F.map (TopCat.ofHom (apm_t03j01_inclusion J)) ≫
        F.map (TopCat.ofHom h.choose) = 𝟙 _
    rw [← F.map_comp]
    change F.map (TopCat.ofHom
      (h.choose.comp (apm_t03j01_inclusion J))) = 𝟙 _
    rw [apm_t03j01_retraction_comp_inclusion_eq_id h]
    exact F.map_id (TopCat.of J)
  intro x y hxy
  have hxy' := congrArg (fun z ↦ apm_t03j01_H1Map h.choose z) hxy
  have hx := congrArg
    (fun q : apm_t03j01_H1 J ⟶ apm_t03j01_H1 J ↦ q x) hcomp
  have hy := congrArg
    (fun q : apm_t03j01_H1 J ⟶ apm_t03j01_H1 J ↦ q y) hcomp
  simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using
    hx.symm.trans (hxy'.trans hy)

lemma apm_t03j01_no_retraction_of_H1Map_zero
    {X : Type} [TopologicalSpace X] {J : Set X}
    (hzero : apm_t03j01_H1Map (apm_t03j01_inclusion J) = 0)
    (hnonzero : ∃ a : apm_t03j01_H1 J, a ≠ 0) :
    ¬apm_t03j01_RetractsOnto J := by
  intro hret
  obtain ⟨a, ha⟩ := hnonzero
  apply ha
  apply apm_t03j01_H1Map_injective_of_retraction hret
  rw [hzero]
  simp

lemma apm_t03j01_H1_nonzero_of_curve
    {X : Type} [TopologicalSpace X] {J : Set X}
    (hcurve : apm_t03j01_IsCurve J) :
    ∃ a : apm_t03j01_H1 J, a ≠ 0 := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  let e : apm_t03j01_H1 Circle ≅ apm_t03j01_H1 J :=
    F.mapIso (TopCat.isoOfHomeo hcurve.some)
  let a := ConstructionTargets.SingularHomologyConcrete.circleSingularH1Generator
  refine ⟨e.hom a, ?_⟩
  intro hz
  apply ConstructionTargets.SingularHomologyConcrete.circleSingularH1Generator_ne_zero
  have := congrArg (fun z ↦ e.inv z) hz
  simpa [a] using this

/-- **LIBRARY boundary.** A tame nonseparating embedded circle in a closed
genus-two surface is a retract. -/
theorem apm_t03j01_nonseparating_curve_retract
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [PathConnectedSpace X] [ChartedSpace apm_t03j01_E2 X]
    [IsManifold apm_t03j01_Model ∞ X]
    (hX : apm_t03j01_HasGenusTwoHomology X)
    (J : Set X)
    (hcurve : apm_t03j01_IsCurve J)
    (hconnected : IsConnected (Jᶜ)) :
    apm_t03j01_RetractsOnto J := by
  sorry

/-- **LIBRARY boundary.** A separating embedded circle in a closed genus-two
surface is null-homologous. -/
theorem apm_t03j01_separating_curve_H1Map_zero
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [PathConnectedSpace X] [ChartedSpace apm_t03j01_E2 X]
    [IsManifold apm_t03j01_Model ∞ X]
    (hX : apm_t03j01_HasGenusTwoHomology X)
    (J : Set X)
    (hcurve : apm_t03j01_IsCurve J)
    (hdisconnected : ¬IsConnected (Jᶜ)) :
    apm_t03j01_H1Map (apm_t03j01_inclusion J) = 0 := by
  sorry

theorem apm_t03j01
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [PathConnectedSpace X] [ChartedSpace apm_t03j01_E2 X]
    [IsManifold apm_t03j01_Model ∞ X]
    (hX : apm_t03j01_HasGenusTwoHomology X)
    (J₁ J₂ : Set X)
    (hcurve₁ : apm_t03j01_IsCurve J₁)
    (hcurve₂ : apm_t03j01_IsCurve J₂)
    (hcut₁ : apm_t03j01_CutsIntoTwicePuncturedTorus J₁)
    (hcut₂ : apm_t03j01_CutsIntoTwoOncePuncturedTori J₂) :
    apm_t03j01_RetractsOnto J₁ ∧
      ¬apm_t03j01_RetractsOnto J₂ := by
  constructor
  · exact apm_t03j01_nonseparating_curve_retract X hX J₁ hcurve₁ hcut₁
  · exact apm_t03j01_no_retraction_of_H1Map_zero
      (apm_t03j01_separating_curve_H1Map_zero X hX J₂ hcurve₂ hcut₂)
      (apm_t03j01_H1_nonzero_of_curve hcurve₂)

#print axioms apm_t03j01
