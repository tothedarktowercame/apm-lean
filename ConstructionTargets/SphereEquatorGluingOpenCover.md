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

The source homotopies are now compiled without the earlier
`Homeomorph.sumProdDistrib` elaboration problem.  Small named maps first prove
continuity of the fixed whole-sphere branch and the flattened band branch.
`continuous_sum_dom` combines these after an explicit
`Homeomorph.prodSumDistrib`, and conjugation by the three source
homeomorphisms gives jointly continuous homotopies on
`unitInterval × leftPreimage`, `unitInterval × rightPreimage`, and
`unitInterval × bothBandPreimage`.

The source endpoint calculations are public and insensitive to subtype
proofs. `leftPieceSourceHomotopy_zero`,
`rightPieceSourceHomotopy_zero`, and
`intersectionPieceSourceHomotopy_zero` prove that all three deformations
start at the identity. The fixed whole-sphere branches are recorded by
`leftPieceSourceHomotopy_fixes_inl` and
`rightPieceSourceHomotopy_fixes_inr`. The four `*_one` lemmas identify each
band branch at time one with `bandProjectionToEquator`, while the four
`*_fixes_*_equator` lemmas prove pointwise equator fixation at every time.
Each branch lemma accepts an arbitrary proof of membership in the named source
subtype, so later quotient pullbacks do not need to normalize dependent proof
terms.

Fiber coherence is proved for all three sources by induction over
`Relation.EqvGen`; each generator case normalizes the explicit branch formulas
and invokes `bandFlatten_glue_compatible`.  Thus equal fibers of each named
piece quotient map remain equal throughout its source homotopy. All three
subtype-valued quotient lifts are now explicit, with proved pullback
equations and continuity obtained from `continuous_lift_prod_right` (time is
the locally compact first factor). The remaining obligations are the
quotient-level endpoint and fixation equations needed to package the three
homotopy equivalences; their source-level counterparts are complete. For
example the left
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
