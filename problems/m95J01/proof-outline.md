# Proof Outline: m95J01

The frozen Lean theorem is present in `lean/Main.lean`. The dimension transport
through the polynomial equivalence is now proved: `finrank ℝ H = n + 1`.
The necessary direction of the operator-range characterization is also
compiled: `T f - f = g` implies `(P g).coeff n = 0`.
Completeness of `H` is now compiled by transporting finite dimensionality
through `P.symm` and applying `FiniteDimensional.complete`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J01.md`

## Remaining boundary

- construct the finite triangular coefficient recursion proving that the
  now-compiled top-coefficient obstruction is sufficient;
- prove the monomial family is linearly independent and its initial segments
  span the polynomial degree filtration;
- apply normalized Gram–Schmidt and package the resulting adapted
  `OrthonormalBasis`.

Mathlib provides `Polynomial.degreeLTEquiv`, coefficient formulas for
derivatives, and normalized Gram–Schmidt extension APIs. No searched artifact
packages the triangular operator-image calculation.
