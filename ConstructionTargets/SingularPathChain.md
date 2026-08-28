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

No homotopy invariance, concatenation formula, Hurewicz homomorphism, or
homology isomorphism is assumed or proved.  The next missing step is an
explicit normalization of the six faces of the two compiled square triangles.
The target now defines `lowerSquareTriangle`, `upperSquareTriangle`, their
postcomposition with a relative path homotopy, and the signed production chain
`pathHomotopyPrismChain`.  Its differential is proved to be the oriented sum
of the two literal alternating face sums.  What remains is to identify the two
diagonal faces, the time-zero/time-one faces, and the constant endpoint faces.
In Mathlib's production *unnormalized* singular complex, a constant
one-simplex is not definitionally the zero chain.  Thus the relative endpoint
conditions do not themselves delete the two side terms: explicit degenerate
two-simplex fillers are additionally required.  Only after those fillers are
constructed can the based-loop homology classes be compared.  Concatenation
subdivision remains a separate later obligation.
