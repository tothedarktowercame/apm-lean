# PathSubdivisionRemovalReconstruction

This target translates one ordinal removal step into one actual
`SingleVertexInsertion`.  `DeletedVertexPresentation` records a monotone target
vertex sequence and identifies the current subdivision vertices with that
sequence after deleting one non-endpoint coordinate by `succAbove`.

`reconstructionSegment` turns the ordinal removal pivot into the required
subdivision segment.  Its `castSucc` and `succ` endpoints are exactly the two
coordinates bracketing the removed point.  Monotonicity supplies the insertion
inequalities.  `refined_vertex_eq_target` then proves pointwise that the
refined subdivision reconstructs the complete target vertex sequence, and
`reachable_refined` supplies the corresponding one-step
`InsertionReachable` certificate.  Side labels and membership proofs are the
ones produced by `SingleVertexInsertion`; none are replaced propositionally.

The remaining recursive seam is carrying the target-coordinate equality and
the subdivision's internal-vertex count through `RemovalDecomposition.tail`.
Once that dependent bookkeeping is packaged, repeated applications of this
one-step theorem yield the desired reconstructed subdivision.  No recursive
reconstruction or left/right merged specialization is claimed here.
