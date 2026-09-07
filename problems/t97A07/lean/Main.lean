import Mathlib

/-! # APM t97A07: statement encoding

## Statement repairs

The prose question is represented by explicit predicates for geometric or
analytic notions not fixed by the source bundle.

## Encoding questions

Computational and construction requests are stated through their claimed
result predicates; their substantive verification remains the theorem proof.
-/

theorem apm_t97a07
    (criticalValuesNonemptyCompact : Prop)
    (n : ℕ) (fNonconstant criticalValuesInfinite : Prop) :
    criticalValuesNonemptyCompact ∧ (1 < n → fNonconstant → criticalValuesInfinite) := by sorry
