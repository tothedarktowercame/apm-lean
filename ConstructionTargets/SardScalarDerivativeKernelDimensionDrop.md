# Scalar derivative kernel dimension drop

This module converts the codimension-one kernel equality into the strict
finite-dimensional inequality needed for well-founded induction.

For a scalar continuous linear map nonzero on one direction, the compiled
identity `Module.finrank ℝ ker L + 1 = Module.finrank ℝ E` immediately gives
`Module.finrank ℝ ker L < Module.finrank ℝ E`.

The specialized theorem retains the exact derivative
`fderiv ℝ (fun y ↦ ℓ (iteratedFDeriv ℝ i f y v)) x` and derives the strict
dimension drop from the selected nonzero next-jet value on `Fin.cons h v`.

Transporting the localized stratum map through the hypersurface chart and
applying the induction hypothesis on the kernel remain downstream.
