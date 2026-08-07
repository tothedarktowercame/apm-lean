import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t01J05: a nowhere-zero one-form and Euler characteristic

## Statement repairs

None.

## Encoding questions

The one-form is a genuine smooth section of the cotangent bundle, using
Mathlib's smooth-vector-bundle API. Orientation is concrete fiberwise
orientation data on the actual tangent spaces. Euler characteristic is the
alternating sum of rational singular-homology dimensions.
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

/-- In dimension zero the frozen alternating sum has exactly one term. -/
lemma apm_t01J05_eulerCharacteristic_zero
    (X : Type) [TopologicalSpace X] :
    apm_t01J05_eulerCharacteristic 0 X =
      (Module.finrank ℚ (apm_t01J05_H 0 X) : ℤ) := by
  simp [apm_t01J05_eulerCharacteristic]
  rfl

/-- The zero-dimensional case reduces precisely to normalization of `H₀` for
the empty underlying space. -/
lemma apm_t01J05_zeroDim_of_empty_H0
    (X : Type) [TopologicalSpace X]
    [ChartedSpace (apm_t01J05_Euclidean 0) X]
    [IsManifold (apm_t01J05_Model 0) (⊤ : ℕ∞) X]
    (omega : apm_t01J05_OneForm (n := 0) X)
    (homega_ne : ∀ x : X, omega x ≠ 0)
    (hH0 : Module.finrank ℚ (apm_t01J05_H 0 X) = 0) :
    apm_t01J05_eulerCharacteristic 0 X = 0 := by
  clear homega_ne omega
  rw [apm_t01J05_eulerCharacteristic_zero, hH0]
  exact_mod_cast rfl

/-- In dimension zero, every cotangent vector is zero; hence a nowhere-zero
one-form forces the manifold to be empty. -/
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

theorem apm_t01j05
    (n : ℕ) (X : Type)
    [TopologicalSpace X]
    [ChartedSpace (apm_t01J05_Euclidean n) X]
    [IsManifold (apm_t01J05_Model n) (⊤ : ℕ∞) X]
    [BoundarylessManifold (apm_t01J05_Model n) X]
    [CompactSpace X]
    (orientation : apm_t01J05_IsOrientation (n := n) X)
    (omega : apm_t01J05_OneForm (n := n) X)
    (homega_ne : ∀ x : X, omega x ≠ 0) :
    apm_t01J05_eulerCharacteristic n X = 0 := by
  /-
  Boundary (closer hop 2): the zero-dimensional geometric obstruction is now
  compiled as `apm_t01J05_isEmpty_of_nowhereZero_zeroDim`.  It unfolds the
  otherwise irreducible `TangentSpace` definition locally, proves every vector
  in the `Fin 0` Euclidean model is zero, and concludes that a nowhere-zero
  one-form forces the underlying zero-manifold to be empty.  This hop further
  proves `apm_t01J05_eulerCharacteristic_zero`, showing that the frozen sum
  has exactly the single `H₀` term in dimension zero, and
  `apm_t01J05_zeroDim_of_empty_H0`, which closes that endpoint from the exact
  remaining normalization `finrank H₀ = 0`.  Thus no alternating-sum or cast
  bookkeeping remains hidden in the endpoint.

  In positive dimension, the remaining bridge is precisely the classical
  differential-topology argument: construct a smooth Riemannian metric,
  convert the nowhere-zero cotangent section to a nowhere-zero tangent vector
  field, apply Poincaré--Hopf (or vanishing of the Euler class), and identify
  that topological Euler characteristic with the frozen alternating sum of
  rational singular-homology finranks. Searches of `LEMMA-INDEX.md`,
  `ConstructionTargets/`, solved manifold artifacts, git history, and
  Mathlib's smooth-section, tangent-bundle, Riemannian-metric, Euler-class,
  characteristic-class, Poincaré--Hopf, and singular-homology APIs found no
  packaged index theorem or Euler-characteristic comparison. Even the empty
  zero-dimensional endpoint additionally needs the singular-homology
  computation of the empty space to normalize the frozen sum.
  -/
  sorry
