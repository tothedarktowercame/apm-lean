# Ordered-vertex cones with explicit coefficients

For `R : Type` with `[CommRing R]` and `V : Type`, `VertexChains R V`
applies the actual simplicial singular-chain functor to the existing
coefficient-independent `vertexSSet V`, with coefficient object
`ModuleCat.of R R`. Both types are universe zero. No topology or finiteness
is required; the cone takes an explicit vertex `b : V` rather than a global
nonemptiness instance.

`vertexGenerator` is the coproduct injection indexed by an ordered tuple
`Fin (n+1) → V`. `vertexGenerator_boundary` proves its alternating-face
boundary directly in `ModuleCat R`. `vertexCone` is the coproduct descent
that prepends `b`, reusing `prependVertex`; `vertexGenerator_vertexCone`
proves the resulting generator equation.

The face-zero and successor-face identities for prepending a vertex prove
`vertexCone_boundary`: on degree `n+1`, cone followed by differential equals
identity minus differential followed by cone. The signs are derived from
the actual alternating-face differential. In degree zero,
`vertexGenerator_cone_zero_boundary` gives the point generator minus the
cone-point generator. This records the augmented boundary behavior without
claiming an unaugmented contraction in degree zero.

The two compiled examples specialize the degree-one identity to integer
and rational coefficients with vertex type `ℝ`.

The source exactly promotes `/tmp/CoefficientVertexCone.lean`, SHA256
`ad8c47fd37db295af2f29889168035d40eeffbb35e9bab0021cba09d1b404e9b`.
Validation includes fixture and canonical compilation, the focused build,
four standard-only printed axiom audits, both coefficient examples, and
placeholder and scope checks.

Affine realization, recursive barycentric subdivision and the natural
singular chain endomorphism remain in the parent probe. This packet proves
no singular subdivision, homotopy to identity, small-chain comparison,
excision or frozen consumer closure.
