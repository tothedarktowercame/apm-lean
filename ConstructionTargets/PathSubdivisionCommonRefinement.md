# PathSubdivisionCommonRefinement

This target packages the sorted, deduplicated union of the vertices of two
`PathTwoOpenSubdivision` certificates as a third certificate.  It proves the
common vertex set has at least two elements, uses `card - 2` as the subdivision
parameter, and chooses each side label from a containing segment of the left
subdivision using `exists_left_segment_containing`.

The exported coordinate lemmas identify every packaged vertex with
`commonVertex`, and identify the located vertices of both original
subdivisions with their original values.

This target does not claim that the common subdivision is obtained by a finite
sequence of `SingleVertexInsertion`s.  That iteration/common-refinement
reachability theorem is the next remaining step before insertion invariance can
be used to compare the two evaluations.
