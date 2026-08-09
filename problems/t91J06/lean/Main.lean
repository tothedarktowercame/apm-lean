import Mathlib

/-!
# APM t91J06

## Statement repairs

None.

## Encoding questions

The unit interval is the actual subtype `[0,1]`. Its displayed interior is
the subset whose underlying real coordinate lies in `(0,1)`. The weak-topology
hypothesis is expressed invariantly: a subset of `X` is closed whenever its
pullback along every embedding is closed in the interval. This is equivalent
to saying that its intersection with every embedded arc is relatively closed.
-/

open Set

abbrev apm_t91J06_I := Set.Icc (0 : ℝ) 1

/-- The points of the unit interval lying in its real-line interior. -/
def apm_t91J06_Iinterior : Set apm_t91J06_I :=
  {x | x.1 ∈ Ioo (0 : ℝ) 1}

def apm_t91J06_stage {X : Type*} (f : ℕ → apm_t91J06_I → X) (n : ℕ) : Set X :=
  f n '' univ

lemma apm_t91J06_stage_compact
    {X : Type*} [TopologicalSpace X] (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n)) (n : ℕ) :
    IsCompact (apm_t91J06_stage f n) := by
  exact isCompact_univ.image (hf n).continuous

lemma apm_t91J06_stage_mono
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior) :
    Monotone (apm_t91J06_stage f) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  rcases hnested n hx with ⟨y, hy, rfl⟩
  exact ⟨y, mem_univ y, rfl⟩

lemma apm_t91J06_exists_mem_stage
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (x : X) : ∃ n, x ∈ apm_t91J06_stage f n := by
  have hx : x ∈ (⋃ n, f n '' (univ : Set apm_t91J06_I)) := by
    rw [hcover]
    exact mem_univ x
  simpa only [mem_iUnion] using hx

/-- Every point lies in the image of the relative interior of a later stage,
not merely in the compact exhaustion. -/
lemma apm_t91J06_exists_mem_stage_interior
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (x : X) : ∃ n, x ∈ f n '' apm_t91J06_Iinterior := by
  obtain ⟨n, hn⟩ := apm_t91J06_exists_mem_stage f hcover x
  exact ⟨n + 1, hnested n hn⟩

/-- Any two points occur simultaneously in the same later interior stage.
This directed common-chart form is stronger than separate pointwise interior
coverage and is the local input needed to compare eventual orientations. -/
lemma apm_t91J06_exists_pair_mem_stage_interior
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (x y : X) :
    ∃ n, x ∈ f n '' apm_t91J06_Iinterior ∧
      y ∈ f n '' apm_t91J06_Iinterior := by
  obtain ⟨nx, hx⟩ := apm_t91J06_exists_mem_stage f hcover x
  obtain ⟨ny, hy⟩ := apm_t91J06_exists_mem_stage f hcover y
  have hmono := apm_t91J06_stage_mono f hnested
  have hxmax : x ∈ apm_t91J06_stage f (max nx ny) :=
    hmono (Nat.le_max_left _ _) hx
  have hymax : y ∈ apm_t91J06_stage f (max nx ny) :=
    hmono (Nat.le_max_right _ _) hy
  exact ⟨max nx ny + 1, hnested (max nx ny) hxmax,
    hnested (max nx ny) hymax⟩

/-- Why this unblocks `apm_t91j06`: this is the missing inductive
orientation/extension step.  It chooses coordinates on every compact stage,
with the coordinate on stage `n + 1` extending the one already chosen on
stage `n`; the expanding symmetric target intervals make room on both sides. -/
theorem apm_t91J06_bridge_compatible_stage_coordinates
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n))
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆
        f (n + 1) '' apm_t91J06_Iinterior) :
    ∃ g : ∀ n, ↥(apm_t91J06_stage f n) ≃ₜ
        Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ),
      ∀ (n : ℕ) (x : X) (hx : x ∈ apm_t91J06_stage f n),
        ((g (n + 1))
            ⟨x, (apm_t91J06_stage_mono f hnested (Nat.le_succ n)) hx⟩ : ℝ) =
          ((g n) ⟨x, hx⟩ : ℝ) := by
  sorry

/-- Why this unblocks `apm_t91j06`: this is the subsequent gluing step.
Compatible coordinates on the compact exhaustion define a single bijection
to the union of the intervals `[-(n+1), n+1] = ℝ`; `hweak` proves its
continuity and compact-stage continuity proves continuity of its inverse. -/
theorem apm_t91J06_bridge_glue_compatible_stage_coordinates
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆
        f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (hweak : ∀ C : Set X, (∀ n, IsClosed (f n ⁻¹' C)) → IsClosed C)
    (g : ∀ n, ↥(apm_t91J06_stage f n) ≃ₜ
      Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ))
    (hcompat : ∀ (n : ℕ) (x : X) (hx : x ∈ apm_t91J06_stage f n),
      ((g (n + 1))
          ⟨x, (apm_t91J06_stage_mono f hnested (Nat.le_succ n)) hx⟩ : ℝ) =
        ((g n) ⟨x, hx⟩ : ℝ)) :
    Nonempty (X ≃ₜ ℝ) := by
  sorry

theorem apm_t91j06
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n))
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (hweak : ∀ C : Set X, (∀ n, IsClosed (f n ⁻¹' C)) → IsClosed C) :
    Nonempty (X ≃ₜ ℝ) := by
  /-
  Boundary (skipped): the informal proof must orient each embedded interval
  compatibly, construct an inductive family of piecewise homeomorphisms onto
  `[-n,n]`, glue them to a bijection `X → ℝ`, and use `hweak` plus the
  compact exhaustion of `ℝ` to prove both directions continuous. I searched
  Mathlib's `Topology.IsEmbedding`, interval `Homeomorph` and
  `PartialHomeomorph` APIs, final/weak topologies, direct limits, compact
  exhaustions, and one-manifold classification results. There is no packaged
  classification of connected noncompact one-manifolds or theorem identifying
  a weak direct limit of intervals with `ℝ`; the needed compatible gluing
  construction would have to be developed from scratch. Since the frozen
  conclusion is one existential homeomorphism, it exposes no honest
  intermediate proposition for a partial proof.

  Closer hop 1 packaged the compact nested exhaustion explicitly as
  `apm_t91J06_stage`, with compactness and monotonicity proved in
  `apm_t91J06_stage_compact` and `apm_t91J06_stage_mono`. Mathlib's
  `CompactExhaustion` API starts from locally compact sigma-compact spaces and
  does not construct compatible interval coordinates from arbitrary embedded
  stages. Its compactly-generated-space API can certify continuity after a map
  has been constructed, but does not supply the required globally compatible
  bijection. Searches of closed siblings and repository history found no such
  construction.

  Closer hop 2 strengthens the exhaustion in a way needed by that gluing.
  `apm_t91J06_exists_mem_stage` compiles pointwise coverage by compact stages,
  and `apm_t91J06_exists_mem_stage_interior` combines coverage with `hnested`
  to prove every point lies in the image of the relative interior of a later
  embedded interval. Thus endpoint-only coverage is eliminated and the stages
  genuinely provide local arc coordinates everywhere. Searches of interval
  embedding extension, ordered-arc orientation, direct-limit, and
  compactly-generated APIs still found no theorem choosing these coordinates
  compatibly across stages. The unresolved bridge is now specifically the
  inductive orientation/extension and global gluing; the frozen statement is
  unchanged.

  Closer hop 3 strengthens local coordinate coverage to a directed common
  chart. `apm_t91J06_exists_pair_mem_stage_interior` uses monotonicity and the
  maximum of two stage indices to prove that any two points of `X` occur
  simultaneously in the relative interior image of one later embedded
  interval. This supplies the common-chart comparison needed to define a
  global order once compatible orientations exist, rather than merely giving
  unrelated pointwise charts. Renewed searches of `LEMMA-INDEX.md`, all
  `ConstructionTargets/`, interval homeomorphism/embedding-extension sources,
  compactly generated spaces, direct limits, and solved topology siblings
  still found no theorem selecting the orientations or extending a coordinate
  across both complementary components. The bridge remains open precisely at
  that choice/extension step and the subsequent gluing.
  -/
  sorry
