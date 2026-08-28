# PathSubdivisionConcatenation

This target supplies the proof-carrying coordinate layer for concatenating two
subdivisions. `concatVertex` keeps every left vertex and then appends only the
noninitial right vertices, so the shared midpoint occurs once. `concatSide`
appends all segment labels. The half-interval maps, endpoint formulas, and
left/right coordinate formulas are proved explicitly.

The exact remaining seam is packaging these coordinates as a
`PathTwoOpenSubdivision`: prove adjacent monotonicity across the unique
midpoint and prove the two families of segment-membership statements by
identifying `Path.trans` subpaths on the rescaled halves. No valid subdivision
or evaluation append formula is claimed yet.
