# Scaled recentered boundary normalization

For a Type 0 real normed vector space E, a positive real radius r and a center p satisfying norm(p)<r, this module constructs the literal scaled boundary z ↦ r • z and its recentered map z ↦ r • z-p into the punctured space. `norm_scaled` establishes constant norm r, giving the uniform gap and avoidance proofs. `normalized_value` identifies radial normalization with normalize(r • z-p).

Coefficients are any Type 0 commutative ring R. Positive radial scaling makes the centered normalized map literally identity. The reviewed geometric boundary-motion theorem then proves `homology_identity` in every natural degree for the recentered normalized map. No finite-dimensionality, nontriviality or orientation assumption is used.

`radialIso` uses the actual sphere-punctured-space homotopy equivalence, oriented from punctured-space homology to sphere homology. `forward_inverse` identifies the actual recentered boundary homology map with its inverse. `boundaryIso` retains that actual forward map; `inverse_right` and `inverse_left` give both compositions with the actual radial-normalization homology map as identities. Integer and rational examples and ten standard-only axiom audits are included. No rank-one assertion about ordinary H0 of S0 is made.

The chart-neighborhood construction supplies r through its positive radius and p through the source-coordinate displacement of a nearby point. Its strict source-radius bound is exactly norm(p)<r. This instantiates the scaled-boundary result, but identification with relative chart normalizations still requires actual pair connecting naturality and neighborhood-inclusion maps.

The Lean source exactly matches fixture SHA256 586c754b4afdb9d0d2a8598b484da1db69308fa4d036b3df1d9ce022b2f28dd7. The relative connecting comparison, nearby transition-unit equality, orientation compatibility and consumer closure remain downstream.
