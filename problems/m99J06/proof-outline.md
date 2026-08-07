# Proof Outline: m99J06

The canonical partial formalization is `lean/Main.lean`, with one documented
boundary remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m99J06.md`

## Compiled progress

- `apm_m99J06_galerkin_energy`: testing the discrete equation with its
  solution gives the exact energy identity.
- Weak solutions are unique by extensionality of the Hilbert inner product.
- `apm_m99J06_galerkin_unique`: two Galerkin solutions coincide, since their
  difference has zero inner product with itself. This proves the coercivity
  half of finite-dimensional solvability.

## Follow-up needed

- Build the representative-level right-hand side as a linear functional and
  apply finite-dimensional Riesz representation plus injective-surjective.
- Establish the custom one-dimensional Sobolev integration-by-parts and
  regularity bridge needed for weak/strong equivalence.
- Obtain a weakly convergent subsequence from the bounded sequence and pass
  the Galerkin equations to its limit using density.
