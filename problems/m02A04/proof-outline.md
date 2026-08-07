# Proof Outline: m02A04

The Lean artifact is complete. It evaluates the translated Gaussian exactly
and derives the ratio limit from eventual equality to one.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02A04.md`

## Formalized

- Exact completed-square identity.
- Centered Gaussian evaluation via `integral_gaussian`.
- Lebesgue translation invariance via `integral_add_right_eq_self`.
- Extraction of the constant factor `exp (t/4)` from the integral.
- The normalization
  `sqrt (π / t³) = sqrt π * Real.rpow t (-3/2)` for positive `t`.
- Exact equality with the stated leading term for every positive `t`.
- Eventual equality of the quotient to one, hence the required limit.

## Remaining Boundaries

None.
