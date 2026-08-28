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

The target also constructs Mathlib's explicit relative contraction of
`c.trans c.symm`, combines its prism with the direct concatenation triangle,
and retains the constant two-simplex correction required by the unnormalized
complex.  The resulting `backtrackingBoundaryChain_boundary` proves that
`pathChain c.symm + pathChain c` is an actual boundary.  The corresponding
backtracking loop has the same H1 class as the constant loop.
The target then uses the already proved constant-loop calculation to state
the resulting H1 class as zero explicitly.

The remaining exact step is to combine the individual closed-edge expansions
over `oneChainSupport` and use `cycle_vertex_balance` to cancel connector
coefficients pointwise.  The subsequent passage from arbitrary homology
representatives to the range of `fundamentalGroupH1Hom` is not claimed here.

No connector cancellation, circulation decomposition, Hurewicz surjectivity,
or Hurewicz injectivity is assumed.
