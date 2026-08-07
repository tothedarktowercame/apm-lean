# Proof Outline: m02A04

The Lean artifact now completes the square, translates the Gaussian integral,
and extracts the exponential factor. Two small finishing boundaries remain.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02A04.md`

## Formalized

- Exact completed-square identity.
- Centered Gaussian evaluation via `integral_gaussian`.
- Lebesgue translation invariance via `integral_add_right_eq_self`.
- Extraction of the constant factor `exp (t/4)` from the integral.

## Remaining Boundaries

- Normalize `sqrt (pi / t^3)` to `sqrt pi * Real.rpow t (-3/2)` with
  explicitly typed `Real.rpow` intermediate identities.
- Reuse the resulting exact formula to make the quotient eventually equal to
  one and close the limit.
