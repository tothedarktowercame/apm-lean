# Single-vertex insertion for two-open subdivisions

`FundamentalGroupoidTwoOpenInsertion.lean` constructs the literal finite-index
tuples obtained by inserting a parameter into one segment of a
`PathTwoOpenSubdivision`.

The new vertex tuple is `Fin.insertNth k.succ.castSucc t S.vertex`; the new side tuple
duplicates `S.side k` at the same position.
This packet compiles the tuple definitions, their inserted/old-entry equations,
and the two interval inequalities as `SingleVertexInsertion`; it does not yet
package those data as a `PathTwoOpenSubdivision`.

This target does not assume refinement invariance.  The remaining bounded
steps are (1) the dependent `Fin.insertNth` endpoint/adjacency normalization
needed to fill the subdivision structure and (2) an arbitrary-position
normalization theorem for `composeFin`: replacing one arrow by the composite
of its two inserted arrows leaves the dependent fold unchanged.  Once those
are available, the banked
`TwoOpenDescentDatum.mapPath_subpath_split` supplies exactly its local arrow
equation and will yield evaluation invariance.

No common-refinement theorem, descent functor, or Seifert--van Kampen result is
claimed here.
