# Proof Outline: t91A07

Fix a fixed point `x` and define `F y = f y - y`. Its derivative at `x` is
`fderiv ℝ f x - id`, which is bijective by nondegeneracy. The bounded inverse
theorem packages this derivative as a continuous linear equivalence.

Smoothness of `F` upgrades its derivative to a strict derivative. Mathlib's
inverse-function theorem then supplies a local inverse and an eventual
left-inverse identity near `x`. Take the set on which that identity holds as
the desired neighborhood. If `y` in this neighborhood is fixed, then
`F y = 0 = F x`; applying the local inverse gives `y = x`.

Checked Lean state: exit 0; no `sorry` remains.
