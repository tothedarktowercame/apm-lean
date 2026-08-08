# Proof Outline: t97J08

## Hop 4 bridge statements

The open work is now isolated into three declarations above the main theorem:

- `apm_t97J08_bridge_beta_cross_derivatives` supplies the final evaluated
  `fderiv` equality in the concrete closedness predicate.
- `apm_t97J08_bridge_unique_windingNumber` classifies every frozen smooth
  punctured loop by a unique integer under the explicit periodic homotopy
  relation.
- `apm_t97J08_bridge_windingNumber_eq_betaIntegral` identifies any such
  integer with the normalized beta integral.

The last two statements combine immediately into the main theorem's unique
existence of an integer satisfying both properties. Their bodies intentionally
remain `sorry` under the statement-only instruction.

The Lean statement uses the concrete angle form, raw derivatives and interval
integral, and a concrete periodic unit-circle homotopy definition of winding
number. One `sorry` remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J08.md`

## Formal route

- Prove closedness by explicit `HasFDerivAt` quotient calculations for the two
  coordinate coefficients.
- `t97J08_sqRadius_ne_zero` closes the denominator side condition away from
  zero, and `t97J08Beta_differentiableAt_coordinates` proves both coefficient
  functions Fréchet-differentiable using the continuous-linear real and
  imaginary projections. The remaining local step is their evaluated
  `fderiv` equality.
- `t97J08_norm_normalizedLoop` proves the normalized loop has norm one, while
  `t97J08_normalizedLoop_periodic` proves it remains `2π`-periodic.
- Lift the normalized periodic loop through the exponential covering
  `ℝ → Circle`.
- Show the lift changes by a unique integer over one period and use it to
  construct the required homotopy to `exp (i n t)`.
- Rewrite the beta integrand as the derivative of the lifted angle and apply
  interval FTC.

## Open boundary

Mathlib has no packaged classification of periodic circle loops by degree and
no theorem identifying that degree with this angle-form integral. The local
closedness calculation also needs explicit real `fderiv` formulas because
`fun_prop` does not normalize the rational complex-coordinate expressions
after a denominator nonzero proof is supplied. The more narrowly inspected
translation-number API applies to monotone degree-one circle homeomorphisms,
not arbitrary loops; general covering homotopy lifting does not package the
required global lift and integer endpoint-displacement classification.
