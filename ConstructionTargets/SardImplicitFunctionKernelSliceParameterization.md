# Implicit-function kernel-slice parameterization

This module gives an exact parameterization of a constant-first-coordinate
slice in a product by its second coordinate.

For any set `t ⊆ F × G`, the intersection of `t` with the slice whose first
coordinate is `c` is the image under `z ↦ (c, z)` of the subset of `G` whose
paired points lie in `t`. The specialization applies this directly to the
target of an exact `ImplicitFunctionData` chart.

Consequently, a localized implicit-function level set transported through its
chart has an explicit domain in the derivative-kernel coordinate alone.
Transport of the nonzero-jet stratum map and source-dimension induction remain
downstream.
