# Proof Outline: a99J03

The canonical Lean attempt now proves that the explicit endpoint
counterexample belongs to `L¹(0,∞)`.

- `apm_a99J03_counterexample_integrableOn` uses bounded support and indicator
  integrability to close the theorem's third conjunct.

## Follow-up Needed

- Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` to prove the
  derivative formula for the Stieltjes transform on `Ioi 0`.
- Iterate the dominated differentiation argument to obtain `ContDiffOn`.
- Use Tonelli and the derivative formula for the `L¹(Ici a)` estimate.
- Specialize the formula to the indicator datum and reduce endpoint failure to
  nonintegrability of `1 / (x * (x + 1))` near zero.
