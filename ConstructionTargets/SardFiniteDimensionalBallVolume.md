# Exact volume of finite-dimensional closed balls

`finiteDimensional_volume_closedBall_formula` exposes the exact Borel add-Haar
volume formula for a closed ball in a nontrivial finite-dimensional real
inner-product space.  In particular, it isolates the radius factor
`ENNReal.ofReal r ^ finrank ℝ E` from the dimension-dependent unit-ball
constant.

The theorem supplies the target-ball volume scaling formula only.  It does not
construct a source cover, bound that cover's cardinality, or combine the source
and Taylor exponents.  The remaining Sard obligation is one quantitative
finite-dimensional source-cover/Taylor target-ball exponent theorem, before
local rank reduction.
