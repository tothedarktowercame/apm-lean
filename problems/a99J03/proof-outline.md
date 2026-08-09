# Proof Outline: a99J03

The canonical Lean attempt now proves that the explicit endpoint
counterexample belongs to `L¹(0,∞)`.

- `apm_a99J03_counterexample_integrableOn` uses bounded support and indicator
  integrability to close the theorem's third conjunct.
- `apm_a99J03_hasDerivAt_kernel` proves the exact pointwise parameter
  derivative `-f y / (x+y)^2`.
- `apm_a99J03_kernel_deriv_bound` proves the uniform local domination by
  `|f y| / (x/2)^2` on `x/2 < z < 3x/2`.
- `apm_a99J03_endpoint_kernel_not_integrable` proves
  `1/(x*(x+1)) ∉ L¹(0,1)` by comparison with `1/x` and Mathlib's exact rpow
  integrability criterion.

## Follow-up Needed

Hop 4 records the remaining mathematics as three precise contracts:

- `apm_a99J03_bridge_smooth_and_deriv` packages dominated differentiation
  and its iteration, yielding both `ContDiffOn` and the exact first derivative.
- `apm_a99J03_bridge_deriv_integrableOn_Ici` states the Tonelli estimate away
  from zero in exactly the form consumed by the main theorem.
- `apm_a99J03_bridge_counterexample_deriv_norm` identifies the norm of the
  explicit counterexample's derivative on `(0,1)` with
  `1 / (x * (x + 1))`; the compiled endpoint lemma then supplies the
  contradiction.

These declarations are intentionally unproved.  Proving them leaves only
routine conjunction and restriction assembly in `apm_a99j03`.
