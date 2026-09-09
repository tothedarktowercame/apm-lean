# Pair maps and natural connecting morphisms

The coefficient ring `R : Type` has `[CommRing R]`. The spaces `X`, `Y`,
`Z : Type` carry arbitrary topologies; all are universe zero. Subsets are
arbitrary, and a map of pairs consists of a continuous map with an explicit
`Set.MapsTo` proof. Exactness and a short-complex morphism are constructed,
not supplied as hypotheses.

`submap` restricts the map to the subspaces. `inclusion_square` proves the
square of its induced singular-chain map and the absolute chain map.
`arrowMap` packages that square; its induced image map makes the absolute
map descend through the actual relative cokernels of
`RelativeSingularCoefficients`. The result is `relativeMap`, with the proved
`projection_square`. These two squares construct `pairMap`, a morphism of
the actual pair short complexes. Epimorphic quotient projections prove
`relativeMap_id` and `relativeMap_comp`.

`connecting R A n` goes from relative homology in degree `n+1` to subspace
homology in degree `n`. Its naturality equation is oriented as follows:
the induced relative homology map followed by the target connecting map
equals the source connecting map followed by the induced subspace homology
map. Generic homological algebra is applied to the constructed `pairMap`
and the proved short exact sequences. The three exactness theorems cover
the subspace term in degree `n`, absolute term in degree `n`, and relative
term in degree `n+1`.

Integer and rational identity examples use the literal closed complex disk
and its boundary. `diskNeg` is a continuous self-map preserving that boundary;
evaluation at `1` proves it is not the identity. The rational example proves
the connecting naturality equation for this actual nonidentity map of pairs.

The source exactly promotes `/tmp/RelativePairNaturality.lean`, SHA256
`75186dfb83701db491a8e971decd2fd69b7be5231418101506f7a50188c96daf`.
Validation includes fixture and canonical compilation, the focused build,
eleven printed standard-only axiom audits, and placeholder and scope checks.

Coefficient-general excision, sphere suspension and degree-one endpoints
remain downstream before the exact rational S2 witnesses. This packet does
not prove a change-of-coefficients theorem, a sphere table or frozen closure.
