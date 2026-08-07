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
