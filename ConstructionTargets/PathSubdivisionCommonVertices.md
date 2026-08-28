# PathSubdivisionCommonVertices

This target constructs the canonical deduplicated finite union of the vertex
sets of two `PathTwoOpenSubdivision` certificates for the same path.
`commonVertexOrderIso` enumerates that union in increasing order.
`locateLeft` and `locateRight` locate every original vertex, with computation
theorems after applying `commonVertex`.  The enumeration is monotone and its
first and last values are proved to be `0` and `1`.

`commonSegmentLeftIndex` and `commonSegmentRightIndex` reconcile the
`card - 1` segment indexing with the `card`-element enumeration.
`no_commonVertex_between` proves that their values are adjacent in the
deduplicated order.  The generic
`exists_segment_containing_of_no_vertex_between` chooses the maximal original
vertex at or below the left endpoint; maximality deliberately selects the
last duplicate, so no strictness assumption on subdivision vertices is used.
It yields `exists_left_segment_containing` and
`exists_right_segment_containing` for every common segment.

No common subordinate subdivision is asserted yet.  The next step is to
choose, for each common segment, one of its containing original segments,
copy that segment's Boolean side label, and restrict its `segment_mem`
certificate to the smaller common interval.  That choice then packages the
common enumeration as a `PathTwoOpenSubdivision`.
