# Implicit-function level-set image

This module records the exact image of a localized level set under an open
partial homeomorphism.

For any chart into a product, the source-localized locus on which the first
chart coordinate equals a fixed value maps precisely to the chart target
intersected with the corresponding constant-first-coordinate slice. The
specialized theorem combines this with the compiled `ImplicitFunctionData`
coordinate identity, so the source locus is stated directly using `leftFun`.

Parameterizing the target slice by the kernel coordinate, transporting the
localized nonzero-jet stratum map, and applying source-dimension induction
remain downstream.
