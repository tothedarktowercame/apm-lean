# HomotopySquareCellBoundary

This target constructs the two L-shaped routes around each closed cell of a
`HomotopySquareGrid`.  The first route follows the bottom edge and then the
right edge; the second follows the left edge and then the top edge.  The first
coordinate is homotopy time and the second is path position.

The previously banked `cellBottomEdge`, `cellRightEdge`, `cellLeftEdge`, and
`cellTopEdge` remain the public edge interface. `cellCoordHomotopy`
interpolates coordinatewise between the corresponding two routes.
`cellCoordHomotopy_mem` proves structurally that every interpolated point stays
in the same closed grid cell.  Composing with the original path homotopy and
the cell's `cell_mem` certificate gives `cellBoundaryHomotopy`, a relative path
homotopy inside the selected subtype `CoverPiece U V (G.side (i,j))`.
`cellEdgeBoundaryHomotopy` presents this result exactly as
`cellBottomEdge.trans cellRightEdge` homotopic to
`cellLeftEdge.trans cellTopEdge`.

`cellEdgeBoundary_quotient_eq` exports equality in the fundamental-groupoid
path quotient. `cellEdgeBoundary_piece_map_eq` applies any
`TwoOpenDescentDatum` piece functor to that equality.

The next packet must assemble these individual cell equalities along a strip,
including the vertical-edge cancellation and endpoint transports, to compare
the bottom and top subdivision evaluations.
