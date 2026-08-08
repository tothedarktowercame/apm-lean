# Proof Outline: a96J05

## Problem

Let 1 ≤ p < q ≤ ∞. Define X = L^p([0,1],ν) + L^q([0,1],ν) with the infimum
norm ‖f‖_X = inf{‖g‖_p + ‖h‖_q : g ∈ L^p, h ∈ L^q, f = g + h}.
Prove: X is a vector space, ‖·‖_X is a norm, X is complete.

## Strategy

Because `[0,1]` has finite measure and `p ≤ q`, `Lp.antitone` embeds `L^q`
into `L^p`. Hence `L^p + L^q = L^p`; this is compiled as
`apm_a96J05_mem_iff_exists_Lp`. This direct identification avoids the
antidiagonal quotient construction. Since the restricted interval has measure
one, exponent monotonicity also makes this identification isometric for the
displayed infimum norm.

## Compiled progress

1. `apm_a96J05_mem_iff_exists_Lp` proves membership is precisely coercion
   from `Lp ℝ p apm_a96J05_measure`.
2. The forward direction converts the `Lq` summand using `Lp.antitone`; the
   reverse direction uses the zero `Lq` summand.
3. `apm_a96J05_antitone_norm_le` installs the probability-measure instance
   and specializes `eLpNorm_le_eLpNorm_of_exponent_le` to prove
   `‖h‖_p ≤ ‖h‖_q`.
4. `apm_a96J05_norm_eq_Lp_norm` proves both `sInf` inequalities. The
   decomposition `(k,0)` gives the upper bound; triangle inequality and the
   preceding exponent comparison give the lower bound.
5. `apm_a96j05` transports vector closure and all norm laws through this
   equality. For completeness, representatives of a frozen-norm Cauchy
   sequence form a Cauchy sequence in `Lp ℝ p`; completeness of `Lp` supplies
   the limit and the same equality transports convergence back.

## Axioms

All proved theorems: `propext, Classical.choice, Quot.sound` (standard).

## Result

The frozen theorem is fully proved with no `sorry`.
