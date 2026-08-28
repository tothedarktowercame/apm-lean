# HomotopySquareUniformGrid

This target constructs a uniform finite grid subordinate to a two-open cover
of a homotopy square.  The first coordinate is homotopy time and the second is
path parameter.  Grid coordinates are `i/N`; their endpoints, strict
monotonicity, and adjacent distance `1/N` are proved explicitly.

Each cell is the product of two adjacent closed coordinate intervals.  Every
cell point is within the chosen Lebesgue radius of its lower-left corner in
both coordinates, so `exists_side_of_coordinatewise_small` supplies a Boolean
label whose chart contains the full cell image.

The next seam is choosing labels for horizontal row segments consistently
when the cells immediately above and below a shared horizontal edge have
different labels.  The cell certificates show both memberships are available
on such an edge, but this target does not yet package row subdivisions or
path-homotopy invariance.
