# DegreeOneHurewiczSurjective

This target constructs the finite product of closed-edge fundamental-group
classes raised to the actual integer coefficients of a production cycle.  It
proves directly that `fundamentalGroupH1Hom` sends this product to the weighted
additive sum of the corresponding loop classes, and relates that element sum
to evaluation of the morphism-valued sum compiled by the closing-path target.

It then extracts a production cycle representative from the concrete
epimorphism `homologyπ`, proves that the reconstructed `ℤ`-generator represents
the same H1 element, and combines this with the closing-path theorem.  Thus
`fundamentalGroupH1Hom` and its abelianized factor are surjective on every
path-connected space.  No injectivity or Hurewicz isomorphism is claimed.

The two maps are Lean `MonoidHom`s rather than morphisms in a concrete
category, so this target states ordinary function surjectivity; it does not
manufacture an unrelated categorical `Epi` instance.
