# SingularPathChain

This target packages a continuous path as the singular one-simplex obtained
from the repository's `stdSimplexHomeomorphUnitInterval`, and then as the
corresponding generator in Mathlib's production integral singular-chain
complex.

It proves the literal formula

```text
d(pathChain gamma) = pointChain y - pointChain x
```

for `gamma : Path x y`.  A based loop therefore lifts canonically to the
degree-one cycles object.  Both path chains and point chains commute with the
production singular-chain map induced by continuous postcomposition.

The target defines the two oriented triangles of the homotopy square and
proves all six face identities.  Their shared diagonal cancels.  Because
Mathlib's production singular complex is unnormalized, the two constant side
edges are removed by subtracting explicit constant two-simplices, rather than
by treating degenerate chains as zero.  The resulting chain has differential
`pathChain delta - pathChain gamma`, which proves equality of the associated
first-homology classes for path-homotopic based loops.

No concatenation formula, Hurewicz homomorphism, or homology isomorphism is
assumed or proved.  The next separate obligation is the interval-subdivision
two-chain relating `pathChain (gamma.trans delta)` to the sum of the two path
chains.
