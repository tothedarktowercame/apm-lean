# Positive ball measure finiteness

`ball_measure_ne_zero_and_ne_top` packages the two denominator conditions used
by the ENNReal packing quotient. A positive-radius ball in a proper
pseudometric Borel space has nonzero measure when the measure is positive on
open sets, and finite measure when it is locally finite.

The proof promotes the compiled fixture unchanged, using
`measure_ball_pos` and `measure_ball_lt_top` directly.

The remaining consumer work is the finite-dimensional ball-volume quotient
simplification, polynomial source-cover bound, and Taylor target-volume
exponent estimate before local rank reduction.
