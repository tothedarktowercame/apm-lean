# Euclidean and sup-metric unit-ball volumes

`EuclideanAndSupUnitBallVolumes.lean` records the four unit-ball volume values
needed by the sphere-cap normalization route.  In dimensions two and three,
the canonical volume of the open Euclidean unit ball is respectively `π` and
`4π/3`.  For the corresponding finite real function spaces with the sup
metric, the values are `4` and `8`.

The file deliberately stops at these volume computations.  Determining the
`addHaarScalarFactor` ratios `π/4` and `π/6`, and transporting those ratios to
raw Hausdorff measures and restricted integrals, remains downstream.
