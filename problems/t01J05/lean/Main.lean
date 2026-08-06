import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t01J05: a nowhere-zero one-form and Euler characteristic

## Statement repairs

None.

## Encoding questions

Mathlib explicitly lists bundled smooth differential forms on manifolds as a
TODO, and it has no manifold-orientation structure.  The predicates
`apm_t01J05_IsSmoothOneForm` and `apm_t01J05_IsOrientation` are therefore
`sorry`-typed placeholders for precisely those two missing notions.  The
one-form itself is not replaced: it is a covector in the genuine tangent
space at every point.  Euler characteristic is encoded as the alternating
sum of rational singular-homology dimensions.
-/

open CategoryTheory
open scoped ContDiff Manifold Topology

noncomputable section

abbrev apm_t01J05_Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t01J05_Model (n : ℕ) :=
  modelWithCornersSelf ℝ (apm_t01J05_Euclidean n)

def apm_t01J05_IsPartitionOfUnitySubordinate
    {n : ℕ} {X ι : Type*}
    [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean n) X]
    (U : ι → Set X) (rho : ι → X → ℝ) : Prop :=
  (∀ i, IsOpen (U i)) ∧
  (⋃ i, U i) = Set.univ ∧
  (∀ i, ContMDiff (apm_t01J05_Model n) (modelWithCornersSelf ℝ ℝ)
    (⊤ : ℕ∞) (rho i)) ∧
  (∀ i x, 0 ≤ rho i x) ∧
  LocallyFinite (fun i ↦ tsupport (rho i)) ∧
  (∀ i, tsupport (rho i) ⊆ U i) ∧
  ∀ x, ∑ᶠ i, rho i x = 1

def apm_t01J05_OneForm {n : ℕ} (X : Type)
    [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean n) X] :=
  ∀ x : X, TangentSpace (apm_t01J05_Model n) x →L[ℝ] ℝ

def apm_t01J05_IsSmoothOneForm {n : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean n) X]
    (_omega : apm_t01J05_OneForm (n := n) X) : Prop := by
  sorry

def apm_t01J05_IsOrientation {n : ℕ} (X : Type)
    [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean n) X] : Prop := by
  sorry

abbrev apm_t01J05_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))

def apm_t01J05_eulerCharacteristic (n : ℕ) (X : Type)
    [TopologicalSpace X] : ℤ :=
  ∑ k : Fin (n + 1),
    (-1 : ℤ) ^ (k : ℕ) * (Module.finrank ℚ (apm_t01J05_H k X) : ℤ)

theorem apm_t01j05
    (n : ℕ) (X : Type)
    [TopologicalSpace X]
    [ChartedSpace (apm_t01J05_Euclidean n) X]
    [IsManifold (apm_t01J05_Model n) (⊤ : ℕ∞) X]
    [BoundarylessManifold (apm_t01J05_Model n) X]
    [CompactSpace X]
    (orientation : apm_t01J05_IsOrientation (n := n) X)
    (omega : apm_t01J05_OneForm (n := n) X)
    (homega : apm_t01J05_IsSmoothOneForm (n := n) omega)
    (homega_ne : ∀ x : X, omega x ≠ 0) :
    apm_t01J05_eulerCharacteristic n X = 0 := by
  sorry
