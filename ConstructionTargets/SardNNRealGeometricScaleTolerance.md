# NNReal geometric-scale tolerance

`ENNReal.exists_nnreal_geometric_scale_pow_lt` chooses an iterate of a positive
`NNReal` contraction at which a finite `ENNReal` constant times a positive
residual power is below any positive tolerance. Its conclusion retains the
exact `ENNReal.ofReal ((q : ℝ) ^ j) ^ d` representation used by the Taylor
covering estimate.

The proof reduces the residual power to the promoted geometric-power tolerance
theorem and uses only standard axioms.

The remaining consumer work is to compose the maximal-separated cover, Taylor
target-cover measure bound, raw exponent normalization, and this scale choice
into the complete quantitative small-image-measure theorem.
