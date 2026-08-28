# Sphere antipodal homology

This target starts the antipodal-degree calculation at the literal
zero-sphere.  It defines the continuous antipodal map, explicit positive and
negative points, direct degree-zero singular-homology coordinates, and the
oriented reduced generator `negative - positive`.  Naturality of the direct
discrete H₀ coordinates proves that antipodal interchange of the two points
sends this generator to its negative.
This is the exponent-one sign for `S⁰`, agreeing with the frozen indexing:
`T94J08Sphere (n + 1)` is `Sⁿ`, whose antipodal degree is
`(-1)^(n + 1)`.

The target also proves the first actual component square in the production
shift.  Antipodal reflection maps the north-pole complement to the south-pole
complement, and `antipodal_relativeProjection_naturality` proves the resulting
absolute-to-relative projection square at chain level;
`antipodal_relativeProjection_homology_naturality` is its homology image.
The reverse map is also explicit: `antipodalNorthSouthHomeomorph` identifies
the two punctured-sphere subspaces, the named north-to-south and south-to-north
relative maps package both directions, and
`antipodal_relativeProjection_reverse_naturality` proves the reverse square
(with a corresponding homology theorem).  Hence the full projection portion
of the production shift is compared without choosing an orientation or sign.

The target now also compares the hemisphere-excision portion.  It defines the
closed upper hemisphere, its open lower complement, the corresponding
punctured lower hemisphere, and the restricted antipodal map between the two
open hemispheres.  `antipodal_excision_continuousMap_square` is the literal
map square for the two excision inclusions.
`antipodal_hemisphereExcision_naturality` derives the chain-map square from
the generic `relativeSingularMap_comp` theorem, and
`antipodal_hemisphereExcision_homology_naturality` is its homology image.
Thus both the projection and hemisphere-excision portions of the production
shift commute with the north-to-south antipodal map.

The first remaining comparison is the coordinate/radial part of the shift.
The production composite uses `openDiskToOpenUpperMap`; its antipodal image
lands in the lower hemisphere.  One must define the lower-hemisphere
coordinate and the negation map on the punctured open disk and prove the
map-level square

```
antipodalOpenUpperToOpenLower n ∘ openDiskToOpenUpperMap n
  = openDiskToOpenLowerMap n ∘ puncturedOpenDiskNegation n.
```

After that square, the radial comparison must calculate the induced action of
disk negation on the boundary-sphere coordinate.  That calculation is where
the next sign in the recurrence occurs; it is not supplied by the excision
naturality proved here.

This module therefore claims the exact base sign only.  It does not assume a
suspension naturality square, an antipodal degree in positive dimension, or
the frozen `t94J08` conclusion.

There is also a statement-level obstruction at the frozen base case.  At
`n = 0` its `T94J08TopHomology 0` is unreduced `H₀(S⁰; ℤ)`, which is
`ℤ ⊕ ℤ`, so the requested isomorphism with `ℤ` does not exist.  The
oriented difference calculated here is the generator of the reduced summand;
it does not turn unreduced `H₀(S⁰; ℤ)` into `ℤ`.  Consequently this target
cannot close the frozen bridge as currently stated, independently of the
remaining north-versus-south shift comparison.
