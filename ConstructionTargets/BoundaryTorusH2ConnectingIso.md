# Boundary-torus H2 connecting coordinate

This target uses the production Mayer--Vietoris union segment in degrees
`2 → 2 → 1`.  Both cover pieces have zero H2 because they are homotopy
equivalent to the circle.  Exactness therefore makes the degree-one
connecting arrow monic.

The previously constructed lift of that connecting arrow to the signed-fold
kernel is already epic.  Its composite with the proved kernel coordinate is
therefore both monic and epic, hence an isomorphism in `AddCommGrpCat`.  This
gives `boundaryTorusH2IsoInt` without assuming the torus homology table.

No section or splitting is chosen.  The next degree-one calculation requires
forming the short exact sequence whose quotient is the signed-fold cokernel.
A splitting may only be invoked after projectivity of that quotient has been
established in the relevant category.
