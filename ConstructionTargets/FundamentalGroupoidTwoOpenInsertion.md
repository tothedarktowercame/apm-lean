# Single-vertex insertion for two-open subdivisions

`FundamentalGroupoidTwoOpenInsertion.lean` constructs the literal finite-index
tuples obtained by inserting a parameter into one segment of a
`PathTwoOpenSubdivision`.

The new vertex tuple inserts at `insertedVertexPosition S k`; the new side
tuple inserts at the matching `insertedSidePosition S k` and duplicates
`S.side k`.
This packet compiles the tuple definitions, their inserted/old-entry equations,
the two interval inequalities as `SingleVertexInsertion`, adjacent-index
monotonicity, and `SingleVertexInsertion.refined`, an actual
`PathTwoOpenSubdivision`.  Its endpoint and segment-membership proofs cover
the two split pieces separately and transport every unchanged segment through
the explicit `Fin.insertNth` coordinates.

This target does not assume refinement invariance.  The remaining bounded
step is an arbitrary-position normalization theorem for `composeFin`:
replacing one arrow by the composite
of its two inserted arrows leaves the dependent fold unchanged.  Once the
coordinates are normalized through that fold, the banked
`TwoOpenDescentDatum.mapPath_subpath_split` supplies exactly its local arrow
equation and will yield evaluation invariance.

No common-refinement theorem, descent functor, or Seifert--van Kampen result is
claimed here.
