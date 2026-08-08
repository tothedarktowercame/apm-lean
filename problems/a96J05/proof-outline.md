# Proof Outline: a96J05

## Problem

Let 1 ≤ p < q ≤ ∞. Define X = L^p([0,1],ν) + L^q([0,1],ν) with the infimum
norm ‖f‖_X = inf{‖g‖_p + ‖h‖_q : g ∈ L^p, h ∈ L^q, f = g + h}.
Prove: X is a vector space, ‖·‖_X is a norm, X is complete.

## Current strategy

Because `[0,1]` has finite measure and `p ≤ q`, `Lp.antitone` embeds `L^q`
into `L^p`. Hence `L^p + L^q = L^p`; this is compiled as
`apm_a96J05_mem_iff_exists_Lp`. This direct identification avoids the
antidiagonal quotient construction.

## Compiled progress

1. `apm_a96J05_mem_iff_exists_Lp` proves membership is precisely coercion
   from `Lp ℝ p apm_a96J05_measure`.
2. The forward direction converts the `Lq` summand using `Lp.antitone`; the
   reverse direction uses the zero `Lq` summand.

## Axioms

All proved theorems: `propext, Classical.choice, Quot.sound` (standard).

## Remaining bridge (1 sorry)

- Prove the displayed `sInf` equals the ordinary `Lp p` norm. The missing
  inequality is the norm comparison for the `Lq` summand after `Lp.antitone`;
  the measure of `[0,1]` is exactly one.
- Transfer the frozen Cauchy criterion through this equality and invoke the
  complete-space instance for `Lp ℝ p`.
