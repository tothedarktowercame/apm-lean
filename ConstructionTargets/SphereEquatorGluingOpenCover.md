# Sphere-equator gluing open cover

This target constructs the open-cover geometry for two standard Euclidean
spheres glued along their final-coordinate equators.  It uses the fixed band
`|height| < 1/2`.

Before quotienting, the left member is the whole left sphere together with a
right equatorial band; the right member is defined symmetrically.  The file
proves that these sets are open, invariant under the generated gluing
equivalence relation, and covering.  It then descends them to open subsets of
the coinduced quotient and computes the preimage of their intersection.

These statements are dimension-generic.  At dimension two their types match
the explicit metric sphere and equator representation used by frozen
`t96A03` (up to the harmless `Fin.last 2`/index `2` coordinate expression).

The file also constructs the normalized height-band contraction.  It leaves
the horizontal coordinates fixed before normalization and multiplies height
by `1-s`.  Squared-norm estimates prove that the raw vector is nonzero and
that normalization remains strictly inside the band.  The resulting joint
homotopy fixes the equator pointwise, ends on the equator, and packages a
homotopy equivalence between the band and the literal equator subtype.

The pointwise equator-fixing equation is used to prove compatibility with an
arbitrary equator gluing homeomorphism at every homotopy time.  The file now
also constructs the three literal restricted quotient maps (left piece,
right piece, and overlap), proves that each is a quotient map using
`IsQuotientMap.restrictPreimage_isOpen`, and supplies `Homeomorph.setCongr`
identifications between their set-theoretic preimage subtypes and the named
`leftPreimage`, `rightPreimage`, and `bothBandPreimage` subtypes.

The source representation prerequisite for that lift is now explicit.  A
generic `subtypeSumHomeomorph` proves that a subtype of a sum whose two branch
predicates are open is homeomorphic to the sum of its branch subtypes.  Its
three specializations identify the left source with `AmbientSphere ⊕ band`,
the right source with `band ⊕ AmbientSphere`, and the overlap source with
`band ⊕ band`.

The immediate remaining source-level step is to transport the identity/band
contractions through these homeomorphisms and `Homeomorph.sumProdDistrib`.
The direct elaboration of that composition currently exhausts Lean's
deterministic heartbeat budget while checking the `Continuous.comp` goal; no
such declaration is retained here.

The next obstruction is the dependent quotient lift, before the
`continuous_lift_prod_left` argument can be applied.  For example the left
deformation must define a function of exact type

```lean
unitInterval × leftOpen n h → leftOpen n h
```

whose pullback along
`namedLeftPieceQuotientMap n h × id` is the piecewise source deformation
(identity on the left sphere and `bandFlatten` on the right band).  A quotient
representative carries only membership of its quotient class in `leftOpen`;
the source-side `bandFlatten` requires the transported proof that a right
representative lies in `equatorialBand`.  Thus the missing construction is a
dependent `Quotient.lift`/`Quotient.inductionOn` with motive carrying this
open-subtype membership, together with its generated-relation coherence.
The already proved `bandFlatten_glue_compatible` is precisely the nontrivial
generator case, so no additional geometric or arbitrary-`h` compatibility
hypothesis is being hidden here.  No homology or Mayer--Vietoris statement is
present.
