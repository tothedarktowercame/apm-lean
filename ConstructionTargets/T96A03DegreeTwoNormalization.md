# t96A03 degree-two normalization

This target supplies the unconditional final representation change in the
degree-two Mayer--Vietoris calculation.  It identifies
`(Fin 2 → ℤ) × ℤ` with `Fin 3 → ℤ`, first as an explicit linear equivalence
and then as an isomorphism in `ModuleCat ℤ`.

It does not assert that the glued space's second homology is the source of
this isomorphism.  That requires extracting a short exact sequence
`0 → ℤ² → H₂ → ℤ → 0` from the production Mayer--Vietoris arrows and applying
a projective splitting theorem.  The first remaining API task is therefore
to package the relevant production exactness statements as a short exact
sequence with the outer sphere-homology identifications.
