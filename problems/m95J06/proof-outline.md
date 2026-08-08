# Proof Outline: m95J06

The frozen Lean theorem is present in `lean/Main.lean`. Its Hilbert-space
conjunct is now isolated as a compiled helper: the norm is differentiable at
every nonzero point by `DifferentiableAt.norm` applied to the identity map.

Closer hop 2 also compiles the finite-range part of the first conjunct. The
custom supremum is attained on nonempty `Fin n`, every coordinate is bounded
by it, and the real-parameter cardinality factor `n^(1/p)` tends to one as
`p → ∞`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J06.md`

## Remaining boundary

- realize the finite sum as an `eLpNorm` for counting measure, or reproduce the
  finite maximum/power-mean squeeze for real exponents;
- assemble the lower and upper finite power-mean inequalities for arbitrary
  positive real exponents, separating the zero-maximum case from the positive
  case and using the newly compiled attained-maximum and cardinality lemmas.

Sibling `a93J04` proves a general finite-measure `eLpNorm` limit, and
`bpm-1-3-1` proves the finite power-mean squeeze for natural exponents. The
The remaining work is now the direct `Real.rpow` squeeze for this theorem's
custom finite sum; the supremum and limiting cardinality sub-bridges are closed.

Closer hop 3 proves the inner upper estimate
`Σ |xᵢ|^p ≤ n · ‖x‖∞^p` for every nonnegative real exponent. It remains to
apply the outer `1/p` power, normalize the positive-maximum branch, and combine
this with the attained-coordinate lower bound.
