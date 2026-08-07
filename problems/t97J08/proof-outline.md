# Proof Outline: t97J08

The Lean statement uses the concrete angle form, raw derivatives and interval
integral, and a concrete periodic unit-circle homotopy definition of winding
number. One `sorry` remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J08.md`

## Formal route

- Prove closedness by explicit `HasFDerivAt` quotient calculations for the two
  coordinate coefficients.
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
after a denominator nonzero proof is supplied.
