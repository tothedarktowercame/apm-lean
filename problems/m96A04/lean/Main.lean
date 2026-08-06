import Mathlib

/-!
# APM m96A04

## Statement repairs

None.

## Encoding notes

The operator `A` is an algebraic `LinearMap`, so continuity is not built into
its type.  The arbitrary function `B` is asserted linear by exhibiting the
corresponding `LinearMap` with the same underlying function.
-/

theorem apm_m96a04
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →ₗ[ℂ] X) (B : X → X)
    (hAB : ∀ x y : X, inner ℂ (A x) y = inner ℂ x (B y)) :
    (∃ Blin : X →ₗ[ℂ] X, (Blin : X → X) = B) ∧ Continuous B ∧ Continuous A := by
  sorry
