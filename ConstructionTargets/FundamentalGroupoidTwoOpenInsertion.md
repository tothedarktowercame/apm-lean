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
layer now has `adjacentChain`, `subdivisionChain`, and
`refinedRestrictedChain`: the last is the refined chain precomposed with
`insertedVertexPosition.succAboveOrderEmb.monotone.functor`.  The remaining
crossing lemma must insert the explicit `eqToHom` object transports between
the restricted chain's endpoint objects and the refined chain objects before
`Functor.map_comp` can identify the skipped map with two adjacent maps.
After that square is proved, `ComposableArrows.naturality'` compares the total
composites and the banked `TwoOpenDescentDatum.mapPath_subpath_split` supplies
the local split-arrow equation.  No duplicate endpoint-naturality theorem is
introduced.

No common-refinement theorem, descent functor, or Seifert--van Kampen result is
claimed here.
