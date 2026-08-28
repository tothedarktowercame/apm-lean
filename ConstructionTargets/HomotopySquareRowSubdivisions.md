# HomotopySquareRowSubdivisions

This target packages every horizontal grid row of a path homotopy as a path
with the original fixed endpoints.  It proves that the first row is the source
path through `map_zero_left` and that the last row is the target path through
`map_one_left`.

For each time strip it constructs bottom and top
`PathTwoOpenSubdivision`s.  Both use the uniform path-coordinate vertices and
the strip's cell labels.  Their segment membership follows from the full cell
certificate by embedding a horizontal edge into the corresponding closed
grid cell.

At a shared intermediate row, adjacent strips can assign different labels.
Subdivision independence reconciles those two certificates.  The next packet
constructs the vertical edge paths and proves the labelled cell-boundary
homotopy needed to compare each strip's bottom and top descent evaluations.
