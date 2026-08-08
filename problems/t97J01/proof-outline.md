# Proof Outline: t97J01

The Lean artifact proves the theorem completely. Any covering map from a
connected space onto a preconnected space is first shown surjective: its range
is open, while an absent fiber has an evenly covered neighborhood disjoint
from the range, making the range closed as well.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J01.md`

## Finite-cover closedness

For each evenly covered neighborhood `U`, the restricted covering is
conjugate through its covering homeomorphism to the first projection
`U × p⁻¹(y) → U`. The fiber is finite and hence compact, so Mathlib's
`isClosedMap_fst_of_compactSpace` proves this restriction closed.
`IsOpenCover.isClosedMap_iff_restrictPreimage` then promotes the local result
to a globally closed map.

For two distinct points downstairs, their finite fibers are disjoint compact
closed subsets of the Hausdorff total space. The compact-set separation API
gives disjoint open neighborhoods of those fibers. Closed-map upper
hemicontinuity (`isClosedMap_iff_kernImage`) descends them to disjoint open
neighborhoods of the original points, proving the base Hausdorff.
