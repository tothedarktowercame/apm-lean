# Proof Outline: m93J04

The frozen Lean theorem is present in `lean/Main.lean`. The two kernel branch
normal forms and the algebraic derivative jump `1 / y²` are now proved.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J04.md`

## Remaining boundary

- turn the set integral on `Ioo 0 1` into interval integrals split at `y`;
- derive value and derivative vanishing at the outer endpoints from compact
  support inside the open interval;
- establish interval integrability for the kernel branches and test-function
  derivatives;
- integrate by parts twice on each side and simplify the inner terms using
  `apm_m93J04_kernel_derivative_jump`.

Mathlib provides the derivatives of `x * log x` and the required integration-
by-parts APIs. Artifact `a02J03` is a model for support-derived endpoint
vanishing, but no searched result packages this second-order weak identity.
