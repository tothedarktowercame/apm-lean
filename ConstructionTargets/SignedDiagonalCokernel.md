# Signed-diagonal cokernel

`SignedDiagonalCokernel.lean` proves in an arbitrary abelian category that
the codiagonal `Z ⊞ Z ⟶ Z` is a cokernel of the signed diagonal
`biprod.lift (𝟙 Z) (-𝟙 Z)`. It packages the universal property, the induced
canonical isomorphism

`cokernel (biprod.lift (𝟙 Z) (-𝟙 Z)) ≅ Z`,

and the normalization saying that the canonical cokernel projection followed
by this isomorphism is literally `biprod.desc (𝟙 Z) (𝟙 Z)`. The signed
diagonal is also exposed as monic via the existing generic biproduct lemma.

The conjugated form accepts arbitrary isomorphisms `i : I ≅ P` and
`j : I ≅ Q`.  It proves directly that `biprod.desc i.inv j.inv` is a
cokernel of `biprod.lift i.hom (-j.hom)`, hence identifies the canonical
cokernel with `I`.  If an epimorphism `r : P ⊞ Q ⟶ X` is exact after that
signed lift, Mathlib's exact-and-epi characterization makes `r` another
cokernel; uniqueness of colimits then gives `X ≅ I`.  An optional coordinate
`I ≅ Z` gives the reusable target form `X ≅ Z`.  No target isomorphism is
assumed.

For t00A01 this supplies only the algebraic quotient identification in the
degree-zero Mayer--Vietoris segment. It does not construct the topological
Mayer--Vietoris sequence, identify its maps with these normalized morphisms,
compute other degrees, or prove the full homology-sphere bridge.
