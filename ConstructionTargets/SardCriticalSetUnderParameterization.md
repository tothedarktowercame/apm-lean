# Critical-set transport under parameterization

This module specializes derivative-criticality transport to the exact `fderiv`
predicate used in the Sard argument.

At every point where both maps are differentiable, nonsurjectivity of the
original derivative implies nonsurjectivity of the derivative of the
composition. A set-level theorem packages this as an inclusion from a
localized preimage of the original critical set into the critical set of the
parameterized map.

The downstream argument must combine this inclusion with lower-dimensional
image nullity and transfer that nullity back to the original localized stratum.
