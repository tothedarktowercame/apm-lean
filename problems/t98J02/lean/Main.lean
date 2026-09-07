import Mathlib

/-! # APM t98J02: statement encoding

## Statement repairs

The prose question is represented by explicit predicates for geometric or
analytic notions not fixed by the source bundle.

## Encoding questions

Computational and construction requests are stated through their claimed
result predicates; their substantive verification remains the theorem proof.
-/

theorem apm_t98j02
    (nonseparatingLifts separatingLifts : Prop) :
    nonseparatingLifts ∧ ¬ separatingLifts := by sorry
