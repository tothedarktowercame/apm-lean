# Signed-diagonal cokernel

`SignedDiagonalCokernel.lean` proves in an arbitrary abelian category that
the codiagonal `Z ⊞ Z ⟶ Z` is a cokernel of the signed diagonal
`biprod.lift (𝟙 Z) (-𝟙 Z)`. It packages the universal property, the induced
canonical isomorphism

`cokernel (biprod.lift (𝟙 Z) (-𝟙 Z)) ≅ Z`,

and the normalization saying that the canonical cokernel projection followed
by this isomorphism is literally `biprod.desc (𝟙 Z) (𝟙 Z)`. The signed
diagonal is also exposed as monic via the existing generic biproduct lemma.

For t00A01 this supplies only the algebraic quotient identification in the
degree-zero Mayer--Vietoris segment. It does not construct the topological
Mayer--Vietoris sequence, identify its maps with these normalized morphisms,
compute other degrees, or prove the full homology-sphere bridge.
