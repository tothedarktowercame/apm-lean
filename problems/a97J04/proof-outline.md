# Proof Outline: a97J04

## Problem

Let f: [0,1] → ℝ be continuous, BV, and AC on [δ,1] for every δ > 0.
Prove f is AC on [0,1].

## Strategy

Two routes from informal solution:
1. **Direct**: V(x)→0 as x→0⁺ (Lemma 1), split test intervals at a₀.
2. **FTC**: BV→f'∈L¹, AC on [δ,1] gives FTC, limit δ→0.

## Current state (closer hop 1; exit 0, 1 sorry)

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

1. `problems/a93J01/lean/Main.lean`: found a compiled FTC proof for the same
   mathematics, but it uses `AbsolutelyContinuousOnInterval`; discarded as a
   direct dependency because this frozen statement uses the custom list
   predicate.
2. Mathlib `Topology/EMetricSpace/BoundedVariation.lean`: found
   `BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right` for the endpoint
   variation limit and `eVariationOn.sum_le_of_monotoneOn_Iic` for finite
   oscillation sums; retained for the direct route.
3. Repository-wide search for `AbsContOn` and this theorem: only this bundle
   defines the custom predicate. No reusable list-partition bridge was found.
4. Git history (`git log -S`): only the initial partial a97J04 commit contains
   this theorem; no later or alternate proof was found.

## Remaining exact bridge

Choose `a` so the variation on `[0,2a]` is below half the requested error and
use `hf_ac a` for the other half. Partition the sorted input list at left
endpoint `< a`. Total length `< a` puts every prefix endpoint below `2a`, so
its oscillation sum is bounded by variation; the suffix is admissible for the
local AC witness. The remaining Lean work is proving that the dependent
`List.get` bounds/order predicates survive this partition and splitting the
two mapped sums. This is an enriched partial boundary, not an assertion that
the statement or route is defective.
