import Mathlib

/-!
# APM a95J04 — meromorphic continuation past a circle of convergence

## Statement repairs

None.

## Encoding questions

None. The extension uses Mathlib's genuine `MeromorphicOn` predicate and its
integer-valued `meromorphicOrderAt`; a pole is an order strictly below zero
and a simple pole has order `-1`. The coefficient sequence is pinned to `f`
by the power-series sum on the unit disk. Radius exactly one is expressed by
absolute convergence at every nonnegative radius below one and failure of
absolute convergence at every radius above one.
-/

open Complex Metric Set Filter
open scoped Topology

noncomputable section

theorem apm_a95j04
    (D : Set ℂ) (hDopen : IsOpen D) (hDconn : IsConnected D)
    (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (a : ℕ → ℂ)
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hseries : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n ↦ a n * z ^ n) (f z))
    (hradius_lt : ∀ r : ℝ, 0 ≤ r → r < 1 →
      Summable (fun n ↦ ‖a n‖ * r ^ n))
    (hradius_gt : ∀ r : ℝ, 1 < r →
      ¬Summable (fun n ↦ ‖a n‖ * r ^ n))
    (hmero : MeromorphicOn f D) :
    (∃ ζ ∈ sphere (0 : ℂ) 1, meromorphicOrderAt f ζ < 0) ∧
    ((∀ ζ ∈ sphere (0 : ℂ) 1,
        meromorphicOrderAt f ζ < 0 → meromorphicOrderAt f ζ = (-1 : ℤ)) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖a n‖ ≤ M) := by
  sorry
