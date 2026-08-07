# Proof Outline: m93J02

The Lean artifact proves the local-to-global seminorm inequality and its
finiteness consequence. It also compiles the zero-function axioms for both
candidate norms. One large analytic/completeness boundary remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J02.md`

## Formalized

- Local seminorm is bounded by global seminorm.
- Global finiteness implies local finiteness.
- The zero function has zero quotient, local/global seminorm, supremum norm,
  and local/global norm.
- Vanishing of the encoded supremum norm forces the function itself to vanish,
  isolating the definiteness core needed by both norm predicates.

## Remaining Boundary

Prove local finiteness implies global finiteness by compactness, construct the
distance-based nonconstant Lipschitz witness for failure of quantitative
control, finish ENNReal norm algebra, and formalize the complete/incomplete
sequence arguments. The arbitrary connected compact set requires using the
continuous distance image rather than assuming it contains a line segment.
Mathlib's `HolderOnWith` and pointwise Hölder APIs do not bridge to the frozen
nested ENNReal `limsup` definition.
