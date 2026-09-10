# ENNReal countable bounds

This module isolates the order arguments needed to assemble the reviewed C1
graph partition. It works directly in `ℝ≥0∞`, so zero and infinite values need
no separate finiteness cases.

`sum_bounds` distributes fixed ENNReal factors across countable sums and sums
termwise lower and upper bounds. `global_bounds` substitutes exact countable
decompositions into that result. Neither theorem assumes summability or
finiteness.

`set_integral_bounds` integrates constant pointwise bounds over a measurable
set using actual set `lintegral`s. Its hypotheses are only measurability of the
set and the two pointwise inequalities. In particular, the proof does not
convert ENNReal values to real numbers or cancel factors.

The zero and infinity examples record the two endpoint cases explicitly. All
five declarations have standard-only axiom audits.

The remaining consumer step instantiates the integral bounds with the reviewed
derivative-density comparisons, combines them with the graph bounds on each
partition piece, sums the resulting inequalities, normalizes their factors,
and applies `ENNRealMultiplicativeSqueeze`. This module does not assert that
geometric assembly or a graph area formula, and it makes no numerical
Hausdorff-normalization or sphere-mass claim.
