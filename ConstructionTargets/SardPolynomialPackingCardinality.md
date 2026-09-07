# Polynomial packing cardinality

`finset_card_le_enlarged_halfRadius_power` converts the exact packing-volume
product estimate into the explicit polynomial bound
`card(s) ≤ ofReal ((2 * R + ρ) / ρ) ^ d`. It uses the reviewed ENNReal quotient,
common-volume cancellation, and enlarged half-radius ratio modules while
preserving the positive-radius and nonzero finite-volume hypotheses.

The remaining consumer work is one maximal-separated source packing
construction and Taylor target-volume exponent estimate before local rank
reduction.
