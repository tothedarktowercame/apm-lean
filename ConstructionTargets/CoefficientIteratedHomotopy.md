# Iterated subdivision homotopies with explicit coefficients

The module reuses `CoefficientEventualSmallness.subdivisionIterate` on actual
singular chains and constructs `smallIterate` by repeated composition of the
reviewed restricted subdivision. The commutative ring R, topological space X
and subset-family index type are universe zero. Both complexes use coefficient
object `ModuleCat.of R R`. The subsets are arbitrary: openness, covering,
connectedness and nonemptiness are not required.

`absoluteHomotopy` and `smallHomotopy` construct homotopies from each iterate
to identity by induction, composing the reviewed one-step homotopies with
previous iterates and then composing homotopies transitively.
`iterate_inclusion` proves restricted iteration followed by actual inclusion
equals inclusion followed by the reviewed absolute iteration.

`absolute_homology_identity` and `small_homology_identity` use these constructed
homotopies to prove identity action on homology for every iteration count and
every degree. Integer and rational interval examples and five printed axiom
audits are included.

The Lean file is an exact promotion of `/tmp/CoefficientIteratedHomotopy.lean`,
SHA256 `caacbdb193d1ac317c55572cea4eff0ddf682761bbafda2742dae6c79769c96a`.

The next step is to apply eventual factorization to actual cycles and bounding
chains to prove surjectivity and injectivity of the inclusion-induced homology
map, then assemble the all-degree isomorphism. This packet does not claim that
the small-chain inclusion induces an isomorphism or close a frozen consumer.
