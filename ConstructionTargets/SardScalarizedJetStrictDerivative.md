# Scalarized jet strict derivative

This module promotes the scalarized fixed-direction iterated jet to the strict
derivative required by the implicit-function chart.

If `f` is `C^(i+1)`, then `iteratedFDeriv ℝ i f` is `C¹`. Evaluation on fixed
directions `v : Fin i → E` and postcomposition with the selected continuous
linear functional `ℓ : F →L[ℝ] ℝ` preserve `C¹`. Over the real field,
Mathlib's `ContDiff.hasStrictFDerivAt` then identifies the strict derivative as
the exact `fderiv` of `y ↦ ℓ (iteratedFDeriv ℝ i f y v)`.

The result preserves the general target, selected scalar component, derivative
order, and fixed-direction representation. Applying the compiled local chart
to source-dimension reduction remains downstream.
