# Homotopy-square cell boundaries

This target constructs the vertical edges of a uniform homotopy grid and the
four boundary paths of each cell.  Each cell-boundary path is valued in the
specific member of the two-open cover selected by the grid certificate.  The
exported application lemmas record the time/path coordinate convention and
make the subtype proofs irrelevant to consumers.

The next theorem is the relative homotopy, inside that same chart, between
`cellBottomEdge.trans cellRightEdge` and
`cellLeftEdge.trans cellTopEdge`.  It requires a continuous reparameterization
of the square between the two L-shaped boundary traversals.  This target does
not assume that homotopy or any van Kampen conclusion.
