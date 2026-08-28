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
`h_*(0,1)`.  The gluing-cover file currently proves the three homotopy
equivalences but does not prove the two naturality squares identifying its
intersection inclusions under those equivalences with `boundaryInclusion` and
`boundaryInclusion ∘ h`.  Without those squares, the already-proved Hurewicz
coordinate formula cannot honestly be rewritten into the production arrow.

Accordingly this target does not claim H1, H2, H3, or higher-degree homology
of the glued space.  It assumes neither the missing comparison nor any part of
the desired homology table.
