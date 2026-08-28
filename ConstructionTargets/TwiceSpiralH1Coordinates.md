# TwiceSpiralH1Coordinates

This target converts the supplied fundamental-group coordinates in the frozen
twice-spiral interface into H1 coordinates without choosing independent H1
bases.  Each H1 coordinate is defined as inverse Hurewicz followed by the
abelianized supplied π1 coordinate.  Consequently Hurewicz naturality makes
the induced H1 coordinate maps equal to the supplied π1 coordinate maps
literally.

For the actual reusable `boundaryInclusion`, the induced H1 map is proved to
be second-coordinate projection.  For a boundary homeomorphism whose first
π1 column is `(1,2)`, the twisted right inclusion is proved to have formula
`(a,b) ↦ 2*a + d*b`, where `d` is defined as the second coordinate of the
image of `(0,1)`.  The two inclusion maps, with the Mayer--Vietoris minus sign
on the right component, therefore assemble to
`(a,b) ↦ (b, -(2*a + d*b))`.

The coefficient `d` is not determined here, and the next algebra does not
need to determine it: the displayed signed arrow has zero kernel and cokernel
`ℤ/2` for every integer `d`.  Those kernel and cokernel calculations are not
proved in this target.  No determinant, glued-space homology,
fundamental-group pushout, or frozen bridge conclusion is assumed or claimed.
