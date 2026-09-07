# ENNReal packing quotient

`ENNReal.le_div_of_mul_le` converts a packing inequality `a * b ≤ c` into
`a ≤ c / b` when the packed-set measure `b` is nonzero and finite.  The proof
is the direct forward implication of Mathlib's `ENNReal.le_div_iff_mul_le`, so
the promoted declaration preserves the compiled fixture's representation and
hypotheses.

The remaining consumer work is the finite-dimensional ball-volume quotient
simplification, polynomial source-cover bound, and Taylor target-volume
exponent estimate before local rank reduction.
