# Scalar derivative kernel dimension

This module records the exact source-dimension decrease supplied by the
scalarized-jet local chart.

A real-valued continuous linear map that is nonzero on one direction is a
nonzero element of the algebraic dual. Mathlib's dual rank-nullity result then
gives `Module.finrank ℝ ker L + 1 = Module.finrank ℝ E`.

The specialized theorem applies this equality to the exact derivative
`L = fderiv ℝ (fun y ↦ ℓ (iteratedFDeriv ℝ i f y v)) x`, deriving nonvanishing
from the selected next-jet value on `Fin.cons h v`.

Invoking the source-dimension induction hypothesis on these kernel coordinates,
proving nonzero-jet stratum nullity, and aggregating the strata remain
downstream.
