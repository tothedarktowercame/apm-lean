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

/-- The complement obtained by cutting along finitely many embedded circles
is open. -/
lemma apm_t00a03_cut_isOpen {F : Type} [TopologicalSpace F] [T2Space F]
    {n : ℕ} (curves : Fin n → apm_t00a03_Curve F)
    (hemb : ∀ i, Topology.IsEmbedding (curves i)) :
    IsOpen (apm_t00a03_cut curves) := by
  rw [apm_t00a03_cut, isOpen_compl_iff]
  exact isClosed_iUnion_of_finite fun i ↦
    by simpa only [image_univ] using
      (isCompact_univ.image (hemb i).continuous).isClosed

/-- On a surface, every component of the cut-open complement is itself open. -/
lemma apm_t00a03_component_isOpen
    {F : Type} [TopologicalSpace F] [T2Space F]
    [ChartedSpace apm_t00a03_E2 F] [IsManifold apm_t00a03_I2 ⊤ F]
    {n : ℕ} (curves : Fin n → apm_t00a03_Curve F)
    (hemb : ∀ i, Topology.IsEmbedding (curves i)) (x : F) :
    IsOpen (connectedComponentIn (apm_t00a03_cut curves) x) := by
  letI : LocallyConnectedSpace F :=
    ChartedSpace.locallyConnectedSpace apm_t00a03_E2 F
  exact (apm_t00a03_cut_isOpen curves hemb).connectedComponentIn

/-- The maximality hypothesis can be used directly for any essential embedded
circle lying in the cut-open complement.  This isolates the precise input that
a future surface-classification argument must apply inside each component. -/
lemma apm_t00a03_parallel_of_range_subset_cut
    {F : Type} [TopologicalSpace F] {n : ℕ}
    (curves : Fin n → apm_t00a03_Curve F)
    (hmax : ∀ c : apm_t00a03_Curve F,
      Topology.IsEmbedding c → ¬apm_t00a03_nullHomotopic c →
      (∀ i, apm_t00a03_disjoint c (curves i)) →
      ∃ i, apm_t00a03_parallel c (curves i))
    (c : apm_t00a03_Curve F) (hc : Topology.IsEmbedding c)
    (hessential : ¬apm_t00a03_nullHomotopic c)
    (hcut : range c ⊆ apm_t00a03_cut curves) :
    ∃ i, apm_t00a03_parallel c (curves i) := by
  apply hmax c hc hessential
  intro i
  rw [apm_t00a03_disjoint, Set.disjoint_left]
  intro x hxc hxi
  have hxcut := hcut hxc
  exact hxcut (mem_iUnion_of_mem i hxi)

/-- Component-local form of `apm_t00a03_parallel_of_range_subset_cut`. -/
lemma apm_t00a03_parallel_of_range_subset_component
    {F : Type} [TopologicalSpace F] {n : ℕ}
    (curves : Fin n → apm_t00a03_Curve F)
    (hmax : ∀ c : apm_t00a03_Curve F,
      Topology.IsEmbedding c → ¬apm_t00a03_nullHomotopic c →
      (∀ i, apm_t00a03_disjoint c (curves i)) →
      ∃ i, apm_t00a03_parallel c (curves i))
    (x : F) (c : apm_t00a03_Curve F) (hc : Topology.IsEmbedding c)
    (hessential : ¬apm_t00a03_nullHomotopic c)
    (hcomponent : range c ⊆ connectedComponentIn (apm_t00a03_cut curves) x) :
    ∃ i, apm_t00a03_parallel c (curves i) := by
  exact apm_t00a03_parallel_of_range_subset_cut curves hmax c hc hessential
    (hcomponent.trans (connectedComponentIn_subset _ _))

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
  /-
  PARTIAL boundary (closer hop 1).  The helpers `apm_t00a03_cut_isOpen` and
  `apm_t00a03_component_isOpen` establish the first structural facts about the
  actual cut surface: compactness of `Circle` and Hausdorffness make each
  embedded image closed, finiteness makes their union closed, and the manifold
  chart supplies local connectedness so every component of the open complement
  is open.

  Completing the theorem requires the classification of compact surfaces with
  boundary (in particular, that a maximal family of pairwise disjoint,
  nonparallel essential circles has three-holed-sphere complementary pieces),
  followed by additivity of Euler characteristic under cutting and the boundary
  incidence count `3P = 2n`.  Searches of `ConstructionTargets/`,
  `LEMMA-INDEX.md`, all closed topology artifacts, Mathlib's manifold,
  connected-component, singular-homology, Euler-characteristic, excision, and
  Mayer--Vietoris APIs, and git history found no surface classification theorem,
  no cutting-along-an-embedded-circle construction, and no bridge computing the
  Euler characteristic of these concrete complements.  The algebraic
  `HomologicalComplex.eulerChar` API does not connect the frozen singular
  homology data to topological cutting.  This full surface-topology development
  remains open.

  CLOSER HOP 2: `apm_t00a03_parallel_of_range_subset_cut` and its component-
  local corollary now extract the exact consequence of maximality needed by a
  classification proof: every essential embedded circle contained in a
  complementary component is parallel to one of the selected curves.  Further
  searches included Jordan/Schoenflies separation, embedded-circle complement,
  locally connected component, and surface-classification APIs.  They returned
  only general connected-component containment/image lemmas; no theorem turns
  this no-new-essential-curve property into a homeomorphism with
  `apm_t00a03_Pants`, nor connects the singular-homology genus hypothesis to
  Euler characteristic under cutting.  Consequently neither frozen conjunct
  can yet be completed without the same missing surface-topology development.
  -/
  sorry
