# Proof Outline: m00A04

The Lean artifact proves the Hilbert-space minimization theorem and the
zero-dimensional PDE case. One positive-dimensional Sobolev boundary remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m00A04.md`

## Formalized

- Complete the square using `InnerProductSpace.toDual` to obtain boundedness,
  the unique strict minimizer, and its Riesz representation identity.
- For `n = 0`, identify the Euclidean domain with a singleton, take `u = F`,
  use the empty gradient, and approximate exactly by a constant test function.
- In every dimension, the zero function with zero gradient satisfies the custom
  `H¹₀` predicate, including its weak-gradient and approximation clauses.

## Remaining Boundary

For `0 < n`, construct the energy completion of compactly supported smooth
tests and prove its completion elements have function/weak-gradient
representatives satisfying the custom approximation predicate. Then apply
Riesz representation and descend the resulting vector to those representatives.
