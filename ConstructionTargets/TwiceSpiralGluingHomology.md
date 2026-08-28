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

The first remaining theorem is the literal equality expressed by
`productionH1ArrowComparisonStatement`: this conjugated arrow must equal
`twiceSpiralSignedArrow d`, where `d` is the second coordinate of
`h_*(0,1)`.

The continuous-map squares are now transported through singular homology by
`intersection_left_homology_square` and
`intersection_right_homology_square`.  The remaining step is the categorical
biproduct association that assembles those two component formulas, including
the Mayer--Vietoris minus sign, into the literal production arrow comparison.

Accordingly this target does not claim H1, H2, H3, or higher-degree homology
of the glued space.  It assumes neither the missing comparison nor any part of
the desired homology table.
