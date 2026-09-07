# Cardinality bound for finite uniform measure estimates

`finset_sum_le_card_mul` converts a uniform `ENNReal` bound on every term of a
finite indexed sum into the corresponding cardinality-times-bound estimate.
For a finite cover indexed by `I`, if every covering-set measure is at most
`b`, their summed measures are at most `I.card * b`.

This theorem performs only the finite-sum aggregation.  It does not construct a
finite-dimensional cover, establish a polynomial bound on its cardinality, or
obtain the target-ball measure exponent from Taylor flatness.  The remaining
Sard obligation is one finite-dimensional polynomial source-cover bound
combined with the Taylor target-ball exponent, before local rank reduction.
