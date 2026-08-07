# Proof Outline: a99J03

The canonical Lean attempt now proves that the explicit endpoint
counterexample belongs to `L¹(0,∞)`.

- `apm_a99J03_counterexample_integrableOn` uses bounded support and indicator
  integrability to close the theorem's third conjunct.
- `apm_a99J03_hasDerivAt_kernel` proves the exact pointwise parameter
  derivative `-f y / (x+y)^2`.
- `apm_a99J03_kernel_deriv_bound` proves the uniform local domination by
  `|f y| / (x/2)^2` on `x/2 < z < 3x/2`.

## Follow-up Needed

- Discharge the measurability and restricted-integrability arguments needed
  to apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` using the two
  compiled kernel lemmas.
- Iterate the dominated differentiation argument to obtain `ContDiffOn`.
- Use Tonelli and the derivative formula for the `L¹(Ici a)` estimate.
- Specialize the formula to the indicator datum and reduce endpoint failure to
  nonintegrability of `1 / (x * (x + 1))` near zero.
