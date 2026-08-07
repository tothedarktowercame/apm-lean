# Proof Outline: a99J09

The proof is a local adaptation of the compiled argument in closed sibling
`a01A09`.

- `apm_a99j09_norm_kernel` proves the exact exponential-kernel norm identity.
- `apm_a99j09_integrand_integrable` chooses the real conjugate exponent and
  applies Hölder after proving the exponential kernel lies in the conjugate
  `Lᵠ` space.
- `apm_a99j09_deriv_bound_integrable` similarly proves integrability of
  `‖f t‖ · t exp (-a t)` on the half-line.
- At each point of the right half-plane, a ball of radius half its real part
  gives a uniform integrable derivative bound.  The theorem
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` then differentiates the
  Laplace integral locally and yields complex differentiability.

## Reuse

The sibling could not be imported because problem bundles are not Lean library
modules, so its two Hölder lemmas and dominated-derivative proof were adapted
locally to the frozen names and restricted measure.
