# Proof Outline: a97J02

## Problem

Let A ⊂ [0,1] be closed. For each N ≥ 1, let b(N) count grid cells
[(n-1)/N, n/N] (1 ≤ n ≤ N) intersecting A. Prove lim b(N)/N = m(A).

## Strategy

Squeeze b(N)/N between m(A) and m(cthickening(1/N, A)):
- Lower bound: A ⊆ U_N (union of counted cells), so m(A) ≤ m(U_N) = b(N)/N.
- Upper bound: U_N ⊆ cthickening(1/N, A), so b(N)/N ≤ m(cthickening(1/N, A)).
- cthickenings ↓ A (closed), so m(cthickening(1/N, A)) → m(A).

## Proved (exit 0, 0 sorries)

Definitions and the complete theorem compile:

1. `tendsto_measure_cthickening_of_isClosed` gives thickening convergence.
2. `measure_biUnion_finset₀` sums the a.e.-disjoint closed grid cells.
3. `max 1 ⌈N*x⌉₊` selects a covering cell when `N ≥ 1`.
4. A point in a counted cell lies within its width `1/N` of a witness in A.
5. `ENNReal.tendsto_toReal` and the order squeeze close the real-valued limit.

The earlier local claim `∀ N, A ⊆ gridUnion A N` was corrected to the needed
`N ≥ 1` form: at `N = 0`, the grid union is empty, so the stronger local claim
is false for nonempty A. This does not change the frozen theorem statement.

## Phase-A hints used
- #1 `math-formalization/separation-function-from-distance`: cthickening/infDist API confirmed.
- #2 `math-informal/monotone-approximation`: decreasing cthickenings is the monotone passage.

## Mid-solve lookups

1. Mathlib `Constructions/BorelSpace/Metric.lean`: found and used
   `tendsto_measure_cthickening_of_isClosed`.
2. Mathlib `Measure/MeasureSpace.lean`: found and used
   `measure_biUnion_finset₀` and the squeeze-related measure APIs.
3. Mathlib thickening source: found and used
   `mem_cthickening_of_dist_le` and boundedness of cthickenings.
4. Repository search for an existing grid-cell proof returned no relevant
   solved neighbor; discarded.
