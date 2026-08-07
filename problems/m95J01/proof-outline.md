# Proof Outline: m95J01

The frozen Lean theorem is present in `lean/Main.lean`. The dimension transport
through the polynomial equivalence is now proved: `finrank ℝ H = n + 1`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J01.md`

## Remaining boundary

- install completeness from the proved finite dimension;
- characterize the image of `P'' - 2P'` by a finite triangular coefficient
  recursion, proving the top-coefficient obstruction is also sufficient;
- prove the monomial family is linearly independent and its initial segments
  span the polynomial degree filtration;
- apply normalized Gram–Schmidt and package the resulting adapted
  `OrthonormalBasis`.

Mathlib provides `Polynomial.degreeLTEquiv`, coefficient formulas for
derivatives, and normalized Gram–Schmidt extension APIs. No searched artifact
packages the triangular operator-image calculation.
