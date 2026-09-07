# Scalarized-jet kernel-parameter smoothness

This module combines the exact scalar implicit-function construction with the
remaining-order regularity of a fixed scalarized iterated derivative.

Under the selected nonzero `Fin.cons` next-jet value, the resulting
`ImplicitFunctionData` exposes its scalarized left function, derivative,
orthogonal-projection right coordinate, and base point. Its inverse-chart
kernel parameter is `ContDiffAt` at any separately supplied remaining order
`n`.

The downstream argument must establish regularity of the original map composed
with this parameterization, transport the localized critical stratum, and apply
source-dimension induction.
