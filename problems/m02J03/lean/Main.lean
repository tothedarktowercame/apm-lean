import Mathlib

/-!
# APM m02J03

## Statement repairs

None.

## Encoding notes

The source indices start at one.  Lean's sequence starts at zero, so the
`n`th convex combination is indexed by `Fin (n + 1)` and uses exactly
`x 0, …, x n`.  The coefficients remain real, strictly positive, and sum to
one as required.
-/

open Filter
open scoped BigOperators Topology

theorem apm_m02j03
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (x : ℕ → H) (x₀ : H)
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y))) :
    (∃ C : ℝ, ∀ n : ℕ, ‖x n‖ ≤ C) ∧
    (Tendsto x atTop (nhds x₀) ↔
      Tendsto (fun n ↦ ‖x n‖) atTop (nhds ‖x₀‖)) ∧
    ∃ α : ∀ n : ℕ, Fin (n + 1) → ℝ,
      (∀ n : ℕ, (∀ i : Fin (n + 1), 0 < α n i) ∧ ∑ i, α n i = 1) ∧
      Tendsto (fun n ↦ ∑ i : Fin (n + 1), (α n i : ℂ) • x i.val)
        atTop (nhds x₀) := by
  sorry
