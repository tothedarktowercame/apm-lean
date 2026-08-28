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

The next required theorem is a comparison between the north-based and
south-based production shifts.  It is not presently a formal consequence of
the definition: the shift is a composite of the north-pole relative
projection, hemisphere excision, open-disk/hemisphere coordinates, radial
comparison, and the pair connecting isomorphism.  None of the banked APIs
states that this whole composite, or its individual relative-pair maps,
commutes with antipodal reflection.  In particular, antipodal exchanges the
north- and south-pole complements used asymmetrically by the construction.
The first remaining square is precise: construct the south-pole analogue of
`relativeExcisionMap northPoleComplement closedLowerHemisphere` and prove that
the antipodal maps of pairs commute with the two excision inclusions.  The
current generic API proves projection naturality for `relativeSingularMap`,
but supplies no composition/naturality theorem for those relative maps, so it
does not yet express this excision square.  Beyond it, antipodal reflection
lands in the lower hemisphere, requiring an explicit lower/upper hemisphere
coordinate and radial comparison before the production shift composites can
be related.

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
