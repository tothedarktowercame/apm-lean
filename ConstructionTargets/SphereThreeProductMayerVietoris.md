# Degree-two homology of `S³ × S³`

`SphereThreeProductMayerVietoris.lean` proves
`IsZero (SingularHomology 2 (TopCat.of (S³ × S³)))` from the reviewed pole
cover and its reviewed homology inputs.

The proof instantiates
`productionMayerVietoris_exact_union U V U_isOpen V_isOpen U_union_V 1`.
Its explicit exact segment is

```text
H₂(U) ⊞ H₂(V)  ⟶  H₂(S³ × S³)  ⟶  H₁(U ∩ V).
```

`coverPieces_singularH2_biprod_isZero` makes the left object zero, and
`intersection_singularH1_isZero` makes the right object zero.  The conclusion
is the canonical `ShortComplex.Exact.isZero_X₂` consequence.

The reviewed cover equality is exported as `U_union_V`; there is no theorem
named `SphereProductPoleOpenCover.cover` in the reviewed geometry commit.
No product-homology, Eilenberg--Zilber, or Künneth result is used.

The next seam is the final `S² × S⁴` versus `S³ × S³` comparison and frozen
`t95J04` wiring; neither is part of this milestone.
