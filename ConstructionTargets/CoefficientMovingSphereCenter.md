# Moving-center sphere boundary homotopy

For a Type 0 real normed vector space E and a center p with norm strictly less than one, this module constructs the actual map z ↦ z-p from the literal unit sphere into the punctured space. `avoid_zero` uses norm(t • p) < 1 for t in the unit interval to prove that z-t • p never vanishes.

`shiftHomotopy` runs from sphere inclusion at t=0 to `shiftedInclusion` at t=1, with continuity and both endpoints proved. `centerFamily` is jointly continuous in the center in the open unit ball and the sphere point; its value is literally z-p. `betweenCenters` reverses the first center homotopy and follows the second.

Coefficients are any Type 0 commutative ring R. `homology_shift` applies actual coefficient singular-homology homotopy invariance. `homology_betweenCenters` proves independence of the center in every natural homology degree. `recenteredSphere` follows shifted inclusion by radial normalization, with value normalize(z-p); `homology_recentered` proves that its induced sphere map is identity using the actual radial-normalization retraction equation. No finite-dimensionality, nontriviality or orientation assumption is imposed, and no rank-one assertion about ordinary H0 of S0 is made.

Integer and rational Euclidean examples and nine standard-only axiom audits are included. The Lean source exactly matches fixture SHA256 39cbabeb13c100817d70e6c1fa61a084cda2311d210eba60e854202762ae79fe.

Comparing the moving boundary through an actual chart transition and identifying its homology equations with relative normalizations at distinct points remain downstream. Arbitrary-chart transition-unit local constancy, relative localization isomorphisms, orientation compatibility and consumer closure are not established here.
