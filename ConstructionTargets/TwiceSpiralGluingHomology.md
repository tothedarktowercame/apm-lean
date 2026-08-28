# TwiceSpiralGluingHomology

This target begins the production Mayer--Vietoris calculation for
`SolidTorusGluingOpenCover.Gluing h`.

Degree zero is complete.  Explicit witnesses make both cover pieces and their
intersection nonempty; their supplied homotopy equivalences transport the
known H0 coordinates for the solid torus and boundary torus.  The production
open-cover H0 theorem therefore yields both additive-group and `ModuleCat ℤ`
isomorphisms with `ℤ`.

In degree one, the target constructs the exact coordinate isomorphisms from
the production intersection and piece homology objects to `ℤ²`, using the H1
coordinates determined by the supplied π1 coordinates.  It also defines
`productionH1CoordinateArrow`, the actual production intersection arrow
conjugated by those isomorphisms.

`productionH1ArrowComparisonStatement` now records the literal equality only
with the three coordinate-normalization premises it needs: the two boundary
inclusions must be second-coordinate maps in the supplied bases, and
`h_*(1,0)=(1,2)`.  Arbitrary choices of the four coordinate equivalences do
not satisfy that statement (for example, negating a solid-torus coordinate
negates the corresponding component).

The continuous-map squares are transported through singular homology by
`intersection_left_homology_square` and
`intersection_right_homology_square`.  The first remaining interface is the
normalization equating each projection of `productionIntersectionArrow`
(defined through `HomologicalComplex.homologyMap` of the production singular
chain map) with the corresponding `singularHomologyFunctor.map` of the
subtype inclusion.  These maps are mathematically the same, but are not
definitionally equal and no public comparison theorem currently rewrites
between the two representations.  After that comparison, the banked
preadditive sign lemmas and `actual_signed_H1_pair_formula` supply the final
biproduct calculation.

Accordingly this target does not claim H1, H2, H3, or higher-degree homology
of the glued space.  It assumes neither the missing comparison nor any part of
the desired homology table.
