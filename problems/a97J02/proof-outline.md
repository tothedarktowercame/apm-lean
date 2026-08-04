# Proof Outline: a97J02

## Problem

Let A ⊂ [0,1] be closed. For each N ≥ 1, let b(N) count grid cells
[(n-1)/N, n/N] (1 ≤ n ≤ N) intersecting A. Prove lim b(N)/N = m(A).

## Strategy

Squeeze b(N)/N between m(A) and m(cthickening(1/N, A)):
- Lower bound: A ⊆ U_N (union of counted cells), so m(A) ≤ m(U_N) = b(N)/N.
- Upper bound: U_N ⊆ cthickening(1/N, A), so b(N)/N ≤ m(cthickening(1/N, A)).
- cthickenings ↓ A (closed), so m(cthickening(1/N, A)) → m(A).

## Proved (exit 0, 5 sorries)

Definitions: `gridCell`, `gridIndices`, `b`, `gridUnion` all compile.
Theorem statement compiles. Proof structure laid out with 5 sorries:

1. **h_cthick_tendsto** (boundary): cthickening(1/N, A) → volume A.
   Needs: antitone, iInter = A (closed), tendsto_measure_iInter_atTop.
2. **h_union_measure** (boundary): volume(gridUnion) = b(N)/N.
   Needs: measure of finite union of intervals with disjoint interiors.
3. **h_A_subset_union** (boundary): A ⊆ gridUnion (grid covers [0,1]).
4. **h_union_subset_cthick** (boundary): gridUnion ⊆ cthickening(1/N, A).
5. **Step 5** (boundary): squeeze argument.

## Phase-A hints used
- #1 `math-formalization/separation-function-from-distance`: cthickening/infDist API confirmed.
- #2 `math-informal/monotone-approximation`: decreasing cthickenings is the monotone passage.

## Mid-solve lookups
None (all API exploration was in Phase A or direct Mathlib grep).
