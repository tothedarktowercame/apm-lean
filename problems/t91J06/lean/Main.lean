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

theorem apm_t91j06
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n))
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (hweak : ∀ C : Set X, (∀ n, IsClosed (f n ⁻¹' C)) → IsClosed C) :
    Nonempty (X ≃ₜ ℝ) := by
  sorry
