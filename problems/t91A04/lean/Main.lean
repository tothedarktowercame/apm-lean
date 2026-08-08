import Mathlib

/-!
# APM t91A04 — Banach fixed-point theorem

The hypotheses directly encode a self-map with contraction constant
`c ∈ [0, 1)` on a nonempty complete metric space.  The conclusion retains
the stronger uniqueness assertion already present in the previous statement.

## Statement repairs

None.

## Encoding questions

None.
-/

theorem apm_t91a04
    {M : Type*} [MetricSpace M] [CompleteSpace M] [Nonempty M]
    {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    {T : M → M} (hT : ∀ x y, dist (T x) (T y) ≤ c * dist x y) :
    ∃! z : M, T z = z := by
  sorry
