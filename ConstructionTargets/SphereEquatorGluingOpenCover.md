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
the locally compact first factor). The source identity formulas descend to
`leftPieceHomotopyMap_zero`, `rightPieceHomotopyMap_zero`, and
`intersectionPieceHomotopyMap_zero`. Continuous retained-subspace maps are
provided by `leftSphereInclusion`, `rightSphereInclusion`, and
`equatorIntersectionInclusion`.

For the left piece, `leftSourceRetraction` maps the retained branch
identically and maps a right-band point through `bandProjectionToEquator`,
`h.symm`, and `equatorInclusion`. `leftSourceRetraction_eq_of_eqv` proves its
compatibility with the generated gluing relation, so `leftPieceRetraction`
descends continuously through the restricted quotient.
`leftPieceRetraction_comp_inclusion` proves the strict retraction equation.

The left endpoint comparison is now complete:

```lean
leftPieceHomotopyMap n h (1, x) =
  leftSphereInclusion n h (leftPieceRetraction n h x)
```

After choosing a source representative, the retained branch is fixed
definitionally. In the band branch, the proof turns
`EquatorGlueRel.glue (h.symm (bandProjectionToEquator n y))` into equality in
the restricted quotient subtype after applying
`leftPieceSourceHomotopy_inr_one`. `leftPieceHomotopy` packages the descended
deformation, and `leftPieceHomotopyEquiv` proves that `leftOpen n h` is
homotopy equivalent to `AmbientSphere n`.

The right piece is now complete by the symmetric construction with the
nontrivial orientation made explicit: `rightSourceRetraction` sends a left
band point through `bandProjectionToEquator`, then `h`, and fixes the retained
right sphere. `rightSourceRetraction_eq_of_eqv` proves compatibility with the
same generated gluing relation. The descended `rightPieceRetraction`, strict
retraction equation, time-one comparison, `rightPieceHomotopy`, and
`rightPieceHomotopyEquiv` prove

```lean
rightOpen n h ≃ₕ AmbientSphere n
```

without importing a symmetry or assuming the endpoint equality. The
intersection retraction, endpoint comparison, and homotopy-equivalence package
remain downstream. No homology or Mayer--Vietoris statement is present.
