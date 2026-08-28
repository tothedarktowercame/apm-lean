# HomotopySquareStripDescent

This target identifies each horizontal grid-cell edge with the corresponding
piece of the bottom or top row subdivision. `rowSegmentOfCell` supplies the
explicit inverse cast from cell columns to row-subdivision segment indices;
the two vertex lemmas normalize its endpoints.

`bottomEdge_ambient_eq_piece` and `topEdge_ambient_eq_piece` prove the path
identifications directly from the shared `Icc.convexCombo` parameterization.

`bottom_mappedPiece_eq_cellMap` and `top_mappedPiece_eq_cellMap` transport
those equalities through `TwoOpenDescentDatum.mapPath`. The path equality is
eliminated before proof irrelevance identifies the membership certificates.
`normalized_cell_square` consequently expresses the banked cell-boundary
square using the actual bottom and top subdivision `mappedPiece`s.

`composeFin_ladder` is a generic finite categorical telescope: a family of
commuting adjacent squares identifies the bottom composite followed by the
last vertical map with the first vertical map followed by the top composite.

The remaining strip specialization must package one vertical morphism for
every `Fin (G.N + 1)` grid vertex. Interior entries must use
`shared_vertical_mapPath_eq` to reconcile the adjacent cell labels; the two
endpoint entries use respectively the first cell's left edge and last cell's
right edge. Those dependent index and endpoint transports are not assumed in
this target.
