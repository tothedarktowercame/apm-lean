# Zero-sphere homology with explicit ring coefficients

For every `R : Type` with `[CommRing R]`, `H R k` is the actual ordinary
singular homology object of `SphereHomology.Sphere 0` in `ModuleCat R`,
using coefficient object `ModuleCat.of R R`. The sphere is the literal
unit-sphere subtype in one-dimensional Euclidean space.

`positivePoint` and `negativePoint` explicitly construct the endpoints with
coordinate `1` and `-1`. `coordinates : Sphere 0 ≃ Bool` uses the proved
sign classification; its inverse sends `true` to the positive endpoint and
`false` to the negative endpoint. Both inverse identities are proved.

`h0Coordinates` constructs `H R 0 ≅ ModuleCat.of R (Bool → R)` by composing
the actual discrete-space singular H0 comparison, the module coproduct to
direct-sum comparison, the finite direct-sum to function-space equivalence,
and reindexing through `coordinates`. Thus ordinary H0 has two independent
coordinates; this is not reduced H0. No field or nontrivial-ring hypothesis
is added. `positive_vanishing` proves `IsZero (H R k)` for every `k > 0`
using total disconnectedness. `rationalH0` and `integralH0` specialize the
same construction to the rational and integer rings.

The source exactly promotes `/tmp/SphereZeroCoefficients.lean`, SHA256
`bbd49dd15fcdee1825971c924948c636ac4d21796c7229c2a568e2d26e2f54dd`.
Validation comprises fixture and canonical compilation, the focused Lake
build, five printed axiom audits allowing only `propext`, `Classical.choice`
and `Quot.sound`, and forbidden-token and exact-scope checks.

This packet calculates the zero-sphere only. Coefficient-general suspension,
the degree-one endpoint, positive-dimensional sphere tables, and the exact
rational S2 witnesses and identity-map equations remain downstream.
Arbitrary-map naturality and frozen consumer closure are not established.
