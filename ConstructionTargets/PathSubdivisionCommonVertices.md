# PathSubdivisionCommonVertices

This target constructs the canonical deduplicated finite union of the vertex
sets of two `PathTwoOpenSubdivision` certificates for the same path.
`commonVertexOrderIso` enumerates that union in increasing order.
`locateLeft` and `locateRight` locate every original vertex, with computation
theorems after applying `commonVertex`.  The enumeration is monotone and its
first and last values are proved to be `0` and `1`.

No common subordinate subdivision is asserted.  The next exact theorem is an
adjacent-interval containment result: each consecutive pair in the common
enumeration must lie between one consecutive pair of `S` (and likewise of
`T`).  That result is required before a side label and `segment_mem`
certificate can be chosen honestly.
