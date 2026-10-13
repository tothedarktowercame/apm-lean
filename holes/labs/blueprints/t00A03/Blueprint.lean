import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.SurfaceClassification

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev apm_t00a03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t00a03_I2 := 𝓘(ℝ, apm_t00a03_E2)
abbrev apm_t00a03_H (k : ℕ) (F : Type) [TopologicalSpace F] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F))

def apm_t00a03_isGenusSurface
    (g : ℕ) (F : Type) [TopologicalSpace F] : Prop :=
  Nonempty (F ≃ₜ ConstructionTargets.Surfaces.Surface true g)

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

abbrev apm_t00a03_Pants :=
  {p : ℝ × ℝ //
    ‖p‖ < 3 ∧ (1 / 2 : ℝ) < ‖p - (-1, 0)‖ ∧
      (1 / 2 : ℝ) < ‖p - (1, 0)‖}

/-- LIBRARY: the compact-surface classification/cutting theorem needed for
the qualitative half of the pants-decomposition theorem. -/
theorem apm_t00A03_pants_components
    (g n : ℕ) (F : Type)
    [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t00a03_E2 F]
    [IsManifold apm_t00a03_I2 (⊤ : ℕ∞) F]
    (hg : 2 ≤ g) (hgenus : apm_t00a03_isGenusSurface g F)
    (curves : Fin n → apm_t00a03_Curve F)
    (hemb : ∀ i, Topology.IsEmbedding (curves i))
    (hessential : ∀ i, ¬apm_t00a03_nullHomotopic (curves i))
    (hdisjoint : ∀ i j, i ≠ j →
      apm_t00a03_disjoint (curves i) (curves j))
    (hnonparallel : ∀ i j, i ≠ j →
      ¬apm_t00a03_parallel (curves i) (curves j))
    (hmax : ∀ c : apm_t00a03_Curve F,
      Topology.IsEmbedding c → ¬apm_t00a03_nullHomotopic c →
      (∀ i, apm_t00a03_disjoint c (curves i)) →
      ∃ i, apm_t00a03_parallel c (curves i)) :
    ∀ x ∈ apm_t00a03_cut curves,
      Nonempty
        (connectedComponentIn (apm_t00a03_cut curves) x ≃ₜ
          apm_t00a03_Pants) := by
  sorry

/-- LIBRARY: Euler characteristic under cutting and the boundary-incidence
count for a maximal essential curve system. -/
theorem apm_t00A03_curve_count
    (g n : ℕ) (F : Type)
    [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t00a03_E2 F]
    [IsManifold apm_t00a03_I2 (⊤ : ℕ∞) F]
    (hg : 2 ≤ g) (hgenus : apm_t00a03_isGenusSurface g F)
    (curves : Fin n → apm_t00a03_Curve F)
    (hemb : ∀ i, Topology.IsEmbedding (curves i))
    (hessential : ∀ i, ¬apm_t00a03_nullHomotopic (curves i))
    (hdisjoint : ∀ i j, i ≠ j →
      apm_t00a03_disjoint (curves i) (curves j))
    (hnonparallel : ∀ i j, i ≠ j →
      ¬apm_t00a03_parallel (curves i) (curves j))
    (hmax : ∀ c : apm_t00a03_Curve F,
      Topology.IsEmbedding c → ¬apm_t00a03_nullHomotopic c →
      (∀ i, apm_t00a03_disjoint c (curves i)) →
      ∃ i, apm_t00a03_parallel c (curves i))
    (hpants : ∀ x ∈ apm_t00a03_cut curves,
      Nonempty
        (connectedComponentIn (apm_t00a03_cut curves) x ≃ₜ
          apm_t00a03_Pants)) :
    n = 3 * g - 3 := by
  sorry

theorem apm_t00a03 :
    ∀ (g n : ℕ) (F : Type)
      [TopologicalSpace F] [T2Space F] [CompactSpace F]
      [PathConnectedSpace F] [ChartedSpace apm_t00a03_E2 F]
      [IsManifold apm_t00a03_I2 (⊤ : ℕ∞) F],
      2 ≤ g → apm_t00a03_isGenusSurface g F →
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
  intro g n F _ _ _ _ _ _ hg hgenus curves hemb hessential hdisjoint
    hnonparallel hmax
  have hpants :=
    apm_t00A03_pants_components g n F hg hgenus curves hemb hessential
      hdisjoint hnonparallel hmax
  exact ⟨hpants,
    apm_t00A03_curve_count g n F hg hgenus curves hemb hessential
      hdisjoint hnonparallel hmax hpants⟩

#print axioms apm_t00a03
