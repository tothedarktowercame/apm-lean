# DegreeOneHurewiczSurjectivity

This bounded target exposes an arbitrary production singular one-chain as its
actual finitely supported `DirectSum` of simplex coefficients.  It also
conjugates the production differential into the degree-one and degree-zero
coefficient presentations and proves that a cycle maps to zero there.

The target owns coherent one- and zero-coefficient
generators as images of the production coproduct injections under the same
coordinate isomorphisms.  It proves their direct-sum normalization and the
literal formula that the coefficient boundary of a one-simplex generator is
its terminal generator minus its initial generator.  No separately chosen
`DecidableEq` instance is compared downstream.

It now also defines the actual finite support of each one-chain, reconstructs
the coefficient family as the sum of its supported generators, and transports
the differential through that sum.  Evaluation at a zero-simplex is defined
directly from the `DirectSum` function value, so it does not expose any
classical equality choice.  Applying that evaluator to a cycle proves the
finite vertex-balance equation: the total coefficients on supported edges
terminating at a vertex equal the total coefficients on supported edges
starting there.

The first remaining algebraic layer is a finite integral circulation
decomposition into loops, followed by path-connected basepoint closing data.
No graph-cycle decomposition, path closing, Hurewicz surjectivity, or Hurewicz
isomorphism is assumed here.
