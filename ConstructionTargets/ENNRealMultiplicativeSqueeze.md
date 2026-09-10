# ENNReal multiplicative squeeze at one

`ENNRealMultiplicativeSqueeze` proves that two-sided multiplicative bounds whose factors approach one force equality in `ℝ≥0∞`.

For every natural exponent `d` and arbitrary `B : ℝ≥0∞`, `upper_tendsto` and `lower_tendsto` prove convergence of

`(ofReal (1 + ε)) ^ d * B` and `(ofReal (1 - ε)) ^ d * B`

to `B` as positive `ε < 1` tends to zero. The proof first sends each real factor through continuous `ofReal`, raises it to the fixed natural power, and then invokes ENNReal multiplication continuity at the limiting factor one. Because one is finite and nonzero, the second factor `B` may be zero, finite, or infinite.

`eq_of_bounds` assumes the corresponding lower and upper bounds for every real `ε` with `0 < ε < 1`. Eventual inequalities on the punctured interval and the two convergence theorems give both orders between `A` and `B`. The proof never converts an ENNReal value to a real number and never cancels a measure or an infinite factor.

The three declarations have standard-only axiom audits. Zero, finite, and infinite values of `B` are covered uniformly by the theorem's arbitrary ENNReal quantifier; no finiteness or nonzero premise is present.

The remaining area argument must use the reviewed measurable graph partition to establish the global bounds for every `ε`, by countable additivity and comparison with the actual derivative density. This module supplies no area formula, numerical Hausdorff normalization, sphere mass, Stokes theorem, period result, or consumer closure.
