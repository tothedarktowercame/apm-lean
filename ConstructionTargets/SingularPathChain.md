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

No Hurewicz homomorphism or homology isomorphism is assumed or proved.  The
production singular prism also proves that a based loop and its barycentric
subdivision differ by a boundary.  The older subdivision normalization seam
is recorded exactly by `PathTransSubdivisionFormula`.
The recursive barycentric subdivision orders the first half as a
barycentre-first edge, so proving that formula requires an explicit
edge-reversal two-simplex before it can identify the subdivision of
`gamma.trans delta` with `pathChain gamma + pathChain delta`.

`pathTrans_difference_boundary_of_subdivision_formula` verifies that this one
orientation/parametrization equation is sufficient to produce the desired
boundary.  It does not treat the equation as established.

The direct-triangle coordinate layer is now compiled independently of that
subdivision normal form.  `intervalConcatenationTriangle` has affine parameter
`z₁ / 2 + z₂`; its three public, proof-insensitive face-value lemmas reduce to
`(1 + u₁) / 2`, `u₁`, and `u₁ / 2`.  These are the exact scalar identities
needed to identify the delta, full-concatenation, and gamma faces.

The direct triangle now identifies all three singular faces and proves the
unconditional production boundary and integral-H1 concatenation formula in
Mathlib's order (`gamma.trans delta` traverses `gamma` and then `delta`).  This
supersedes the earlier literal `PathTransSubdivisionFormula`, which is not
asserted: production subdivision represents its first half as the negative of
the reversed edge, not literally as the forward edge.  No Hurewicz theorem is
claimed.
