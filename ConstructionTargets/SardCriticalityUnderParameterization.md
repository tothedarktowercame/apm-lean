# Criticality under parameterization

This module records the derivative-criticality transport used by the
source-dimension Sard induction.

Precomposing a nonsurjective continuous linear map with any continuous linear
map remains nonsurjective. Combined with the `HasFDerivAt` chain rule, a
critical point of a map therefore remains critical after a smooth
parameterization of its source.

The downstream argument must instantiate this result on each scalarized-jet
kernel parameterization, apply lower-dimensional Sard nullity, and aggregate
the localized strata.
