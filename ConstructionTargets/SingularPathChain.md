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
explicit singular two-chain/prism showing that relatively homotopic path
chains differ by a boundary, followed separately by the subdivision identity
relating a concatenated path chain to the sum of its two pieces.
