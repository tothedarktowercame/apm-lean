# First-derivative projected chart formula

`exists_projected_localRankNormalForm_with_formula` constructs the projected
local rank chart without discarding its forward coordinate identity.

The first coordinate is exactly the orthogonal projection of the original map
onto the range of the base derivative. The second is exactly orthogonal
projection of the source point onto the kernel of that projected derivative.
The theorem also retains membership of the base point in the chart source.

This formula is the input needed to differentiate constant first-coordinate
slices. The remaining consumer step combines their kernel tangency with the
rank-at-most residual-flatness theorem and proves local image nullity.
