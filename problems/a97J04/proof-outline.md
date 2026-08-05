# Proof Outline: a97J04

## Problem

Let f: [0,1] → ℝ be continuous, BV, and AC on [δ,1] for every δ > 0.
Prove f is AC on [0,1].

## Strategy

Two routes from informal solution:
1. **Direct**: V(x)→0 as x→0⁺ (Lemma 1), split test intervals at a₀.
2. **FTC**: BV→f'∈L¹, AC on [δ,1] gives FTC, limit δ→0.

## Proved (exit 0, 1 sorry)

- `AbsContOn` definition (from scratch; Mathlib has no function-level AC)
- Statement compiles and is faithful to problem
- 1 sorry: main proof body

## Boundary

The main proof requires:
1. Variation vanishing: eVariationOn f (Icc 0 a₀) < ε/2 (using BV + continuity at 0)
2. AC on [a₀,1]: apply hypothesis for some fixed a₀ > 0
3. Splitting: cut intervals at a₀, bound each group
-- (Memory: e-codexpilot-extend-local-absolute-continuity-to-an-endpoint-via-the-derivative-primitive)
--    confirms FTC route as alternative
-- (Memory: e-codexpilot-order-a-disjoint-interval-family-into-a-variation-partition)
--    ordering intervals for oscillation bound

APIs searched: eVariationOn, BoundedVariationOn (FOUND), AbsContOn (NOT in Mathlib, defined),
integral_eq_sub_of_hasDerivAt (FOUND), ae_differentiableAt_of_mem_uIcc (FOUND).

## Phase-A hints used
- #1 `e-codexpilot-extend-local-absolute-continuity-to-an-endpoint-via-the-derivative-primitive`: cited.
- #3 `e-codexpilot-order-a-disjoint-interval-family-into-a-variation-partition`: cited.

## Mid-solve lookups
None beyond Phase A.
