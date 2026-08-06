import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t00A03 — pants decompositions

## Statement repairs

The printed `3g-g` is corrected to `3g-3`, as required by the Euler
characteristic and boundary counts and confirmed by the source solution.

The former encoding omitted the surface and encoded the conclusion of part
(a) in its `pantsAtomic` hypothesis.  The repaired statement uses an actual
compact connected surface, embedded circles, concrete null-homotopy and
free-homotopy tests for essentiality and parallelism, and the actual connected
components of the complement.  Genus is pinned by integral singular homology.
-/

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev apm_t00a03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t00a03_I2 := 𝓘(ℝ, apm_t00a03_E2)
abbrev apm_t00a03_H (k : ℕ) (F : Type) [TopologicalSpace F] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F))

def apm_t00a03_hasGenus (g : ℕ) (F : Type) [TopologicalSpace F] : Prop :=
  Nonempty (apm_t00a03_H 0 F ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t00a03_H 1 F ≅ ModuleCat.of ℤ (Fin (2 * g) → ℤ)) ∧
  Nonempty (apm_t00a03_H 2 F ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t00a03_H k F)

abbrev apm_t00a03_Curve (F : Type) := Circle → F

def apm_t00a03_nullHomotopic {F : Type} [TopologicalSpace F]
    (c : apm_t00a03_Curve F) : Prop :=
  ∃ (H : ℝ × Circle → F) (p : F),
    ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ (univ : Set Circle)) ∧
    (∀ z, H (0, z) = c z) ∧ (∀ z, H (1, z) = p)

def apm_t00a03_parallel {F : Type} [TopologicalSpace F]
    (c d : apm_t00a03_Curve F) : Prop :=
  ∃ (e : Circle ≃ₜ Circle) (H : ℝ × Circle → F),
    ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ (univ : Set Circle)) ∧
    (∀ z, H (0, z) = c z) ∧ (∀ z, H (1, z) = d (e z))

def apm_t00a03_disjoint {F : Type} (c d : apm_t00a03_Curve F) : Prop :=
  Disjoint (range c) (range d)

def apm_t00a03_cut {F : Type} {n : ℕ}
    (curves : Fin n → apm_t00a03_Curve F) : Set F :=
  (⋃ i, range (curves i))ᶜ

/-- A concrete model of the interior of a three-times-punctured sphere. -/
abbrev apm_t00a03_Pants :=
  {p : ℝ × ℝ //
    ‖p‖ < 3 ∧ (1 / 2 : ℝ) < ‖p - (-1, 0)‖ ∧
      (1 / 2 : ℝ) < ‖p - (1, 0)‖}

theorem apm_t00a03 :
    ∀ (g n : ℕ) (F : Type)
      [TopologicalSpace F] [T2Space F] [CompactSpace F]
      [PathConnectedSpace F] [ChartedSpace apm_t00a03_E2 F]
      [IsManifold apm_t00a03_I2 ⊤ F],
      2 ≤ g → apm_t00a03_hasGenus g F →
      ∀ curves : Fin n → apm_t00a03_Curve F,
        (∀ i, Topology.IsEmbedding (curves i)) →
        (∀ i, ¬apm_t00a03_nullHomotopic (curves i)) →
        (∀ i j, i ≠ j → apm_t00a03_disjoint (curves i) (curves j)) →
        (∀ i j, i ≠ j → ¬apm_t00a03_parallel (curves i) (curves j)) →
        (∀ c : apm_t00a03_Curve F,
          Topology.IsEmbedding c → ¬apm_t00a03_nullHomotopic c →
          (∀ i, apm_t00a03_disjoint c (curves i)) →
          ∃ i, apm_t00a03_parallel c (curves i)) →
        (∀ x ∈ apm_t00a03_cut curves,
          Nonempty
            (connectedComponentIn (apm_t00a03_cut curves) x ≃ₜ
              apm_t00a03_Pants)) ∧
        n = 3 * g - 3 := by
  sorry
