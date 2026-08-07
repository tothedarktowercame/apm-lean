# Proof Outline: m93J01

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J01.md`

## Closer hop 1 progress

- The coefficient `κ = 1/12` is definitional.
- The new helper `apm_m93J01_schrodinger_residual_eq` proves that part (b)'s
  residual is pointwise identical to part (a)'s centered Taylor residual.
- The remaining analytic bridge is a finite-order `ContDiff` Taylor theorem in
  neighborhood-filter `IsBigO` form. Mathlib's direct Taylor `IsBigO` theorem
  is for analytic functions; its finite-order mean-remainder theorems require
  converting interval bounds and `taylorWithinEval` coefficients manually.
- Once symmetric sixth- and fourth-order estimates are available, part (b)
  reuses the helper, while the Numerov clause follows by the ODE substitution
  and standard Big-O algebra.

## Closer hop 2 progress

- Mathlib's `taylor_isLittleO_univ` is in fact finite-order and applies
  directly to `ContDiff`; this supersedes the interval remainder route.
- `apm_m93J01_taylor6_isLittleO` transports that theorem along `h ↦ x + h`
  and proves the exact sixth-order expansion with `iteratedDeriv`
  coefficients.
- The remaining closure is symmetric cancellation (including composition by
  negation), weakening little-o to big-O, the order-four specialization for
  `iteratedDeriv 2 y`, and the final already-reduced Numerov algebra.
