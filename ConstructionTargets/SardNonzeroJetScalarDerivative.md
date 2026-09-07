# Nonzero-jet scalar derivative

This module identifies the derivative of a fixed-direction scalar component of
an iterated Fréchet derivative.

For a `ContDiff ℝ (i + 1)` map, fixed directions `v : Fin i → E`, and a
continuous linear functional `ℓ : F →L[ℝ] ℝ`, the scalar function
`y ↦ ℓ (iteratedFDeriv ℝ i f y v)` has the derivative obtained by composing
the derivative of `iteratedFDeriv` with evaluation at `v` and then with `ℓ`.
Pointwise, its value on a varying direction `h` is exactly the next iterated
derivative evaluated at `Fin.cons h v`.

This preserves the derivative order and direction convention needed downstream.
Packaging the resulting nonzero derivative into a local implicit-function
hypersurface, followed by source-dimension reduction, remains separate.
