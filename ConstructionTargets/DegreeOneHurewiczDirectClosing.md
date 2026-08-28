# DegreeOneHurewiczDirectClosing

This target implements the geometric part of the direct closing-path route to
degree-one Hurewicz surjectivity.  It converts every production singular
one-simplex to a path using the inverse standard-simplex/unit-interval
homeomorphism and proves that converting back recovers the original simplex
and production chain generator.

For a path-connected space it chooses a path from a fixed basepoint to every
point and defines the based loop obtained by traversing the initial connector,
the singular edge, and the reverse terminal connector.  Two explicit
concatenation triangles prove the chain-boundary comparisons that expand this
loop into those three path chains.

The remaining exact step is reverse-connector normalization: prove, in the
unnormalized production singular complex, that `pathChain c.symm + pathChain c`
is a boundary.  After that equation, the two compiled concatenation boundaries
give the individual closed-edge formula.  Summing it over `oneChainSupport`
and applying `cycle_vertex_balance` cancels connector coefficients pointwise.
The subsequent passage from arbitrary homology representatives to the range
of `fundamentalGroupH1Hom` is therefore not claimed here.

No circulation decomposition, reverse-edge relation, Hurewicz surjectivity,
or Hurewicz injectivity is assumed.
