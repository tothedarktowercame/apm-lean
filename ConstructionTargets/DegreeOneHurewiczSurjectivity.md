# DegreeOneHurewiczSurjectivity

This bounded target exposes an arbitrary production singular one-chain as its
actual finitely supported `DirectSum` of simplex coefficients.  It also
conjugates the production differential into the degree-one and degree-zero
coefficient presentations and proves that a cycle maps to zero there.

The next missing algebraic layer is a generator formula for
the finite vertex-balance relation and the subsequent graph-cycle
decomposition.  The target now owns coherent one- and zero-coefficient
generators as images of the production coproduct injections under the same
coordinate isomorphisms.  It proves their direct-sum normalization and the
literal formula that the coefficient boundary of a one-simplex generator is
its terminal generator minus its initial generator.  No separately chosen
`DecidableEq` instance is compared downstream.

No vertex balance, cycle decomposition, path-connected closing data, or
Hurewicz surjectivity is assumed here.
