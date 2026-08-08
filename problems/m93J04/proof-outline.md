# Proof Outline: m93J04

The frozen Lean theorem is present in `lean/Main.lean`. The two kernel branch
normal forms and algebraic derivative jump `1 / y²` are proved. Test-function
values and first derivatives now vanish at both outer endpoints; the set
integral splitting and second-derivative normalization also compile.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J04.md`

## Remaining boundary

- establish interval integrability for the kernel branches and test-function
  derivatives;
- integrate by parts twice on each side and simplify the inner terms using
  `apm_m93J04_kernel_derivative_jump`.

Mathlib provides the derivatives of `x * log x` and the required integration-
by-parts APIs. The endpoint and integral-conversion bookkeeping has been
localized, but no searched result packages the remaining second-order branch
calculation.
