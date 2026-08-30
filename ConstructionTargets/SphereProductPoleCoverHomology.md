# Homology of the sphere-product pole cover

This target packages the zero groups needed immediately before applying the
production Mayer--Vietoris exact segment to the reviewed pole cover of
`S³ × S³`.

- `U_homologyIsoS3` and `V_homologyIsoS3` explicitly transport integral
  `AddCommGrpCat` singular homology through the reviewed homotopy equivalences
  `U ≃ₕ S³` and `V ≃ₕ S³`.
- `U_singularH2_isZero` and `V_singularH2_isZero` use the banked off-top-degree
  sphere computation `H₂(S³)=0`.
- `coverPieces_singularH2_biprod_isZero` packages the zero biproduct required
  by Mayer--Vietoris.
- `intersection_homologyIsoSphereTwoProdSphereThree` keeps the reviewed
  `(U ∩ V) ≃ₕ S² × S³` comparison explicit.
- `intersection_singularH1_isZero` installs simple connectivity for `S²`,
  `S³`, and their product, then uses the generic simply-connected `H₁`
  vanishing theorem.

No coefficient-category conversion, Mayer--Vietoris exactness, or frozen
problem theorem is introduced here.
