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

  Closer hop 1 packages the compact nested exhaustion explicitly as
  `apm_t91J06_stage`, with compactness and monotonicity proved in
  `apm_t91J06_stage_compact` and `apm_t91J06_stage_mono`. Mathlib's
  `CompactExhaustion` API starts from locally compact sigma-compact spaces and
  does not construct compatible interval coordinates from arbitrary embedded
  stages. Its compactly-generated-space API can certify continuity after a map
  has been constructed, but does not supply the required globally compatible
  bijection. Searches of closed siblings and repository history found no such
  construction. Thus the unresolved bridge remains the inductive orientation,
  extension, and gluing of stage homeomorphisms; the frozen statement is
  unchanged.
  -/
  sorry
