import Mathlib

/-! # APM t93A01: open sets as cozero sets

## Statement repairs

None.
-/

open Set

theorem apm_t93a01
    {X : Type*} [TopologicalSpace X] [NormalSpace X] [T2Space X]
    [SecondCountableTopology X] (U : Set X) (hU : IsOpen U) :
    (∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ U = ⋃ n, C n) ∧
    (∃ f : X → Set.Icc (0 : ℝ) 1, Continuous f ∧
      (∀ x ∈ U, 0 < (f x : ℝ)) ∧
      ∀ x ∉ U, f x = 0) := by
  sorry
