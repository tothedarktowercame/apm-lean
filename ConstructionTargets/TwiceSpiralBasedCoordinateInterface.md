# Twice-spiral based coordinate interface

`ofCoordinateHypotheses` packages the frozen twice-spiral data into
`BasedTwiceSpiralCoordinateInterface`.

The left induced map is the second-coordinate projection by `hinc₁`.  The
right map is first transported by `h` and then included in the right solid
torus; `boundaryCoordinateMap_second_formula` gives
`2*a + d*b`, where `d` is `twiceSpiralSecondCoefficient`.

The right basepoint is literally `boundaryInclusion (h z₀)`.  It is not
identified with `boundaryInclusion z₀`, and no basepoint-change path is
introduced because the frozen coordinate hypotheses already use the correct
two distinct basepoints.

The next theorem needed for the automorphism-group calculation is a generic
extraction result: evaluation at a chosen object must turn the coordinate
groupoid pseudopushout equivalence into the pushout of the two automorphism
groups along the based leg homomorphisms.  No such extraction is asserted in
this packet.
