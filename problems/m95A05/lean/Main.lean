import Mathlib

/-!
# APM m95A05: coercivity on a reflexive Banach space

## Statement repairs

None.

## Encoding questions

Mathlib does not package topological reflexivity as a typeclass. It is encoded
directly and without weakening as surjectivity of the canonical continuous
linear isometry `V → V''`.
-/

noncomputable section

theorem apm_m95a05
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (hrefl : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V))
    (A : V →L[ℝ] StrongDual ℝ V)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v)
    (f : StrongDual ℝ V) :
    ∃! u : V, A u = f := by
  sorry
