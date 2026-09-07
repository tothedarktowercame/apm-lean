import Mathlib

/-! # APM t99A04: statement encoding

## Statement repairs

The prose question is represented by explicit predicates for geometric or
analytic notions not fixed by the source bundle.

## Encoding questions

Computational and construction requests are stated through their claimed
result predicates; their substantive verification remains the theorem proof.
-/

theorem apm_t99a04
    (integral : ℝ) (separating : Prop)
    (separatingForcesZero nonseparatingCanBeNonzero : Prop) :
    (separating → integral = 0) ∧ separatingForcesZero ∧ nonseparatingCanBeNonzero := by sorry
