# Proof Outline: m02A01

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02A01.md`

## Closer hop 1 findings

- Weak-limit uniqueness, strong-to-weak convergence, and failure of strong
  convergence for the `ℓ²` basis are already complete.
- Weak convergence of the `ℓ²` basis is complete. The proof applies the generic
  weak-bilinear convergence criterion, represents each functional using
  `InnerProductSpace.toDual`, obtains coordinate decay from
  `(lp.memℓp y).summable` and `Summable.tendsto_atTop_zero`, and evaluates basis
  pairings with `lp.inner_single_right`.
- For finite-dimensional weak-to-strong convergence, the natural attempt to
  apply `LinearMap.continuous_of_finiteDimensional` to the inverse weak-space
  identity fails because `WeakSpace` has the weak topological-module structure,
  not the normed-space structure expected by that API. A transported finite
  basis/coordinate proof remains the viable route.
