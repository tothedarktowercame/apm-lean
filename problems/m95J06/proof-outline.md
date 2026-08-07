# Proof Outline: m95J06

The frozen Lean theorem is present in `lean/Main.lean`. Its Hilbert-space
conjunct is now isolated as a compiled helper: the norm is differentiable at
every nonzero point by `DifferentiableAt.norm` applied to the identity map.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J06.md`

## Remaining boundary

- realize the finite sum as an `eLpNorm` for counting measure, or reproduce the
  finite maximum/power-mean squeeze for real exponents;
- identify the finite-range `sSup` with the maximum/essential supremum;
- transport the exponent limit through `ENNReal.ofReal`, or prove directly
  that the cardinality factor raised to `1 / p` tends to one.

Sibling `a93J04` proves a general finite-measure `eLpNorm` limit, and
`bpm-1-3-1` proves the finite power-mean squeeze for natural exponents. The
remaining work is the representation bridge to this theorem's custom real
functions.
