# Implicit-function level-set kernel parameterization

This module parameterizes a source-localized level set directly by the right
coordinate of an open partial homeomorphism.

The map `z ↦ e.symm (c, z)`, restricted to the second-coordinate values whose
paired points lie in the chart target, has image exactly the chart source
where the first coordinate equals `c`. The specialization combines this with
the exact `ImplicitFunctionData.leftFun` coordinate identity, yielding the
original localized left level set.

For the scalarized-jet chart, the right-coordinate space is the derivative
kernel and has strictly smaller source dimension. Pulling back the localized
stratum map and applying source-dimension induction remain downstream.
