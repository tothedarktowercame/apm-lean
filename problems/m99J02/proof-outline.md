# Proof Outline: m99J02

The canonical Lean attempt is `lean/Main.lean`. It proves continuity of the
glued kernel, cancellation of the regular differential expression away from
the gluing point, and constancy of the Wronskian.

- `apm_m99j02_g_continuous` proves the two branches agree continuously at `y`,
  excluding a delta-prime contribution.
- `apm_m99j02_g_hasDerivWithinAt_Iic` and
  `apm_m99j02_g_hasDerivWithinAt_Ioi` prove the exact left and right
  derivatives at the gluing point.
- `apm_m99j02_g_derivative_jump` identifies right minus left with the
  Wronskian, closing the singular coefficient calculation.
- `hregular_cancel` proves `g'' + qg = 0` away from `y`.
- `apm_m99j02_wronskian_eq_zero` proves Abel's identity for the raw derivative
  encoding.
- `apm_m99j02_integrable_mul_test` proves integrability of continuous
  coefficients multiplied by compactly supported smooth tests, enabling the
  boundary-free whole-line integration-by-parts theorem.

## Remaining Boundary

- Split or encode the two smooth branches around `y`.
- Apply interval integration by parts twice on each branch.
- Cancel value boundary terms using kernel continuity and identify the first
  derivative jump with the Wronskian.
