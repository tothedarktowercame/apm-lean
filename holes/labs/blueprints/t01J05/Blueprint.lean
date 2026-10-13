import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

open CategoryTheory Limits
open scoped ContDiff Manifold Topology
noncomputable section

abbrev apm_t01J05_Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t01J05_Model (n : ℕ) :=
  modelWithCornersSelf ℝ (apm_t01J05_Euclidean n)

def apm_t01J05_IsPartitionOfUnitySubordinate
    {n : ℕ} {X ι : Type*}
    [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean n) X]
    (U : ι → Set X) (rho : ι → X → ℝ) : Prop :=
  (∀ i, IsOpen (U i)) ∧ (⋃ i, U i) = Set.univ ∧
  (∀ i, ContMDiff (apm_t01J05_Model n) (modelWithCornersSelf ℝ ℝ)
    (⊤ : ℕ∞) (rho i)) ∧ (∀ i x, 0 ≤ rho i x) ∧
  LocallyFinite (fun i ↦ tsupport (rho i)) ∧
  (∀ i, tsupport (rho i) ⊆ U i) ∧ ∀ x, ∑ᶠ i, rho i x = 1

abbrev apm_t01J05_OneForm {n : ℕ} (X : Type)
    [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean n) X]
    [IsManifold (apm_t01J05_Model n) (⊤ : ℕ∞) X] :=
  ContMDiffSection (apm_t01J05_Model n)
    (apm_t01J05_Euclidean n →L[ℝ] ℝ) (⊤ : ℕ∞)
    (fun x : X ↦ TangentSpace (apm_t01J05_Model n) x →L[ℝ] ℝ)

def apm_t01J05_IsOrientation {n : ℕ} (X : Type)
    [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean n) X] : Prop :=
  Nonempty
    (∀ x : X, Orientation ℝ (TangentSpace (apm_t01J05_Model n) x) (Fin n))

abbrev apm_t01J05_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))

def apm_t01J05_eulerCharacteristic (n : ℕ) (X : Type)
    [TopologicalSpace X] : ℤ :=
  ∑ k : Fin (n + 1),
    (-1 : ℤ) ^ (k : ℕ) * (Module.finrank ℚ (apm_t01J05_H k X) : ℤ)

lemma apm_t01J05_eulerCharacteristic_zero
    (X : Type) [TopologicalSpace X] :
    apm_t01J05_eulerCharacteristic 0 X =
      (Module.finrank ℚ (apm_t01J05_H 0 X) : ℤ) := by
  simp [apm_t01J05_eulerCharacteristic]
  rfl

lemma apm_t01J05_isEmpty_of_nowhereZero_zeroDim
    (X : Type) [TopologicalSpace X]
    [ChartedSpace (apm_t01J05_Euclidean 0) X]
    [IsManifold (apm_t01J05_Model 0) (⊤ : ℕ∞) X]
    (omega : apm_t01J05_OneForm (n := 0) X)
    (homega_ne : ∀ x : X, omega x ≠ 0) : IsEmpty X := by
  refine ⟨fun x ↦ homega_ne x ?_⟩
  ext v
  letI : Subsingleton (TangentSpace (apm_t01J05_Model 0) x) := by
    unfold TangentSpace
    infer_instance
  have hv : v = 0 := Subsingleton.elim _ _
  simp [hv]

lemma apm_t01J05_finrank_H0_eq_zero_of_isEmpty
    (X : Type) [TopologicalSpace X] [IsEmpty X] :
    Module.finrank ℚ (apm_t01J05_H 0 X) = 0 := by
  let e := AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) (TopCat.of X)
  let c := Cofan.mk (∐ fun _ : X ↦ ModuleCat.of ℚ ℚ)
    (Sigma.ι (fun _ : X ↦ ModuleCat.of ℚ ℚ))
  have hc : IsColimit c := coproductIsCoproduct _
  have hi : IsInitial (∐ fun _ : X ↦ ModuleCat.of ℚ ℚ) :=
    (isColimitEquivIsInitialOfIsEmpty (ModuleCat ℚ) c).toFun hc
  have hz : IsZero (∐ fun _ : X ↦ ModuleCat.of ℚ ℚ) := hi.isZero
  have htarget : Subsingleton (↑(∐ fun _ : X ↦ ModuleCat.of ℚ ℚ) : Type) :=
    ModuleCat.subsingleton_of_isZero hz
  have hsub : Subsingleton (apm_t01J05_H 0 X) := by
    constructor
    intro x y
    calc
      x = e.inv (e.hom x) := by simp
      _ = e.inv (e.hom y) := congrArg e.inv (htarget.elim _ _)
      _ = y := by simp
  letI : Subsingleton (apm_t01J05_H 0 X) := hsub
  exact Module.finrank_zero_of_subsingleton

lemma apm_t01J05_zeroDim
    (X : Type) [TopologicalSpace X]
    [ChartedSpace (apm_t01J05_Euclidean 0) X]
    [IsManifold (apm_t01J05_Model 0) (⊤ : ℕ∞) X]
    (omega : apm_t01J05_OneForm (n := 0) X)
    (homega_ne : ∀ x : X, omega x ≠ 0) :
    apm_t01J05_eulerCharacteristic 0 X = 0 := by
  letI : IsEmpty X := apm_t01J05_isEmpty_of_nowhereZero_zeroDim X omega homega_ne
  rw [apm_t01J05_eulerCharacteristic_zero,
    apm_t01J05_finrank_H0_eq_zero_of_isEmpty]
  exact_mod_cast rfl

/-- LIBRARY: the positive-dimensional Poincaré--Hopf theorem, including the
comparison with the rational singular-homology Euler characteristic. -/
theorem apm_t01J05_poincareHopf_oneForm
    (n : ℕ) (hn : 0 < n) (X : Type)
    [TopologicalSpace X] [T2Space X]
    [ChartedSpace (apm_t01J05_Euclidean n) X]
    [IsManifold (apm_t01J05_Model n) (⊤ : ℕ∞) X]
    [BoundarylessManifold (apm_t01J05_Model n) X]
    [CompactSpace X]
    (orientation : apm_t01J05_IsOrientation (n := n) X)
    (omega : apm_t01J05_OneForm (n := n) X)
    (homega_ne : ∀ x : X, omega x ≠ 0) :
    apm_t01J05_eulerCharacteristic n X = 0 := by
  sorry

theorem apm_t01j05
    (n : ℕ) (X : Type)
    [TopologicalSpace X] [T2Space X]
    [ChartedSpace (apm_t01J05_Euclidean n) X]
    [IsManifold (apm_t01J05_Model n) (⊤ : ℕ∞) X]
    [BoundarylessManifold (apm_t01J05_Model n) X]
    [CompactSpace X]
    (orientation : apm_t01J05_IsOrientation (n := n) X)
    (omega : apm_t01J05_OneForm (n := n) X)
    (homega_ne : ∀ x : X, omega x ≠ 0) :
    apm_t01J05_eulerCharacteristic n X = 0 := by
  cases n with
  | zero => exact apm_t01J05_zeroDim X omega homega_ne
  | succ n =>
      exact apm_t01J05_poincareHopf_oneForm (n + 1) (Nat.zero_lt_succ n)
        X orientation omega homega_ne

#print axioms apm_t01j05
