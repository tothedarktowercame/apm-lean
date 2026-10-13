import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces

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

## Genus encoding (revised 2026-10-12)

The source's "a closed orientable surface of genus `g`" names a homeomorphism class, so the hypothesis is a
homeomorphism to the standard polygon model
`ConstructionTargets.Surfaces.Surface true g` (the 4g-gon with word
a₁b₁a₁⁻¹b₁⁻¹⋯). The earlier encoding by integral singular homology of a compact
smooth 2-manifold picks out the same class only via the classification of
surfaces, which the source uses as background and never asks for (Joe,
2026-10-12). The remaining manifold instances are kept; every closed
topological surface admits a smooth structure, so they exclude nothing.
-/

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev apm_t00a03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t00a03_I2 := 𝓘(ℝ, apm_t00a03_E2)
abbrev apm_t00a03_H (k : ℕ) (F : Type) [TopologicalSpace F] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F))

/-- `a closed orientable surface of genus `g``: homeomorphic to the standard polygon model. -/
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
    [ChartedSpace apm_t00a03_E2 F] [IsManifold apm_t00a03_I2 (⊤ : ℕ∞) F]
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

/-- The connected components indexed by points of the cut cover the entire
cut-open surface. -/
lemma apm_t00a03_iUnion_components_eq_cut {F : Type} [TopologicalSpace F]
    {n : ℕ} (curves : Fin n → apm_t00a03_Curve F) :
    (⋃ x : ↥(apm_t00a03_cut curves),
      connectedComponentIn (apm_t00a03_cut curves) x) =
        apm_t00a03_cut curves := by
  apply Set.Subset.antisymm
  · exact iUnion_subset fun x => connectedComponentIn_subset _ _
  · intro x hx
    exact mem_iUnion_of_mem (⟨x, hx⟩ : ↥(apm_t00a03_cut curves))
      (mem_connectedComponentIn hx)

/-- Two component sets of the cut that meet are equal. This supplies the
partition compatibility needed for any future boundary-incidence count. -/
lemma apm_t00a03_components_eq_of_inter_nonempty
    {F : Type} [TopologicalSpace F] {n : ℕ}
    (curves : Fin n → apm_t00a03_Curve F) {x y : F}
    (hxy : (connectedComponentIn (apm_t00a03_cut curves) x ∩
      connectedComponentIn (apm_t00a03_cut curves) y).Nonempty) :
    connectedComponentIn (apm_t00a03_cut curves) x =
      connectedComponentIn (apm_t00a03_cut curves) y := by
  rcases hxy with ⟨z, hzx, hzy⟩
  exact (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm

lemma apm_t00a03_components_eq_or_disjoint
    {F : Type} [TopologicalSpace F] {n : ℕ}
    (curves : Fin n → apm_t00a03_Curve F) (x y : F) :
    connectedComponentIn (apm_t00a03_cut curves) x =
        connectedComponentIn (apm_t00a03_cut curves) y ∨
      Disjoint (connectedComponentIn (apm_t00a03_cut curves) x)
        (connectedComponentIn (apm_t00a03_cut curves) y) := by
  by_cases h : (connectedComponentIn (apm_t00a03_cut curves) x ∩
      connectedComponentIn (apm_t00a03_cut curves) y).Nonempty
  · exact Or.inl (apm_t00a03_components_eq_of_inter_nonempty curves h)
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    exact not_nonempty_iff_eq_empty.mp h

/-- Why this unblocks `apm_t00a03`: this is the missing compact-surface
classification step. It says that maximality of the essential, disjoint,
nonparallel curve family forces every complementary component to be the
interior of a pair of pants. -/
theorem apm_t00A03_bridge_1
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

/-- Why this unblocks `apm_t00a03`: this is the missing global
Euler-characteristic and boundary-incidence calculation for cutting a genus
`g` surface along the maximal curve family; it yields the frozen numerical
conclusion independently of the component homeomorphisms. -/
theorem apm_t00A03_bridge_2
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

  CLOSER HOP 3 packages the complementary-component decomposition needed by a
  future classification and incidence argument. The compiled theorem
  `apm_t00a03_iUnion_components_eq_cut` proves that components indexed by cut
  points cover the whole complement. `apm_t00a03_components_eq_of_inter_nonempty`
  and `apm_t00a03_components_eq_or_disjoint` prove that two such component
  sets are equal whenever they meet, and otherwise disjoint. Combined with
  hop 1's openness and hop 2's no-new-essential-curve consequence, the cut is
  now formally available as an open partition into maximal connected pieces.

  Renewed inspection of connected-component quotients, surface manifold
  sources, singular homology, and Euler-characteristic APIs found no theorem
  promoting these partition properties to a pants homeomorphism or assigning
  finite component/boundary counts. Thus the remaining gap is still the
  genuine compact-surface classification and Euler-characteristic-under-cutting
  development; it cannot be discharged from the newly completed point-set
  partition facts alone.
  -/
  intro g n F _ _ _ _ _ _ hg hgenus curves hemb hessential hdisjoint
    hnonparallel hmax
  exact
    ⟨apm_t00A03_bridge_1 g n F hg hgenus curves hemb hessential hdisjoint
        hnonparallel hmax,
      apm_t00A03_bridge_2 g n F hg hgenus curves hemb hessential hdisjoint
        hnonparallel hmax⟩
