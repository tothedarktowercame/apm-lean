# Proof Outline: m96J06

The Lean artifact formalizes the restricted continuous-function Banach space,
the bounded linear involution, and the core pointwise quadratic estimate. The
fixed-point assembly remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96J06.md`

## Formalized

- Both half-shifted arguments remain in `[-2,2]`.
- The quadratic term preserves restricted continuity and satisfies the
  pointwise two-radius Lipschitz estimate.
- The linear part is bundled on `C(Icc (-2) 2, ℝ)` as a continuous linear map,
  has norm bound three, and is its own inverse.

## Remaining Boundary

Bundle the quadratic map on the continuous-map space, lift the pointwise bound
to the sup norm, restrict the fixed-point map to the closed ball of radius
`1/12`, and apply `ContractingWith.exists_fixedPoint'`.
