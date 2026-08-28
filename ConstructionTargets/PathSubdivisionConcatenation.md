# PathSubdivisionConcatenation

This target supplies the proof-carrying coordinate layer for concatenating two
subdivisions. `concatVertex` keeps every left vertex and then appends only the
noninitial right vertices, so the shared midpoint occurs once. `concatSide`
appends all segment labels. The half-interval maps, endpoint formulas, and
left/right coordinate formulas are proved explicitly.

`concatVertex_monotone` handles the unique transition from the left half to
the right half explicitly.  `trans_subpath_left_apply` and
`trans_subpath_right_apply` identify the two rescaled subpath families
pointwise, including the midpoint branch of `Path.trans`.  The four segment
coordinate lemmas then transport the original membership certificates, and
`concatSubdivision` packages a genuine `PathTwoOpenSubdivision (p.trans q)`.

The remaining seam is algebraic: prove that `TwoOpenDescentDatum.evaluate` of
`concatSubdivision S T` is the categorical composite of the two original
evaluations.  This requires a dependent `composeFin` append theorem and
endpoint-transport normalization; neither is assumed here.
