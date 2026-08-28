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

The target defines `adjacentChain`, `subdivisionChain`, and
`refinedRestrictedChain`: the last is the refined chain precomposed with
`insertedVertexPosition.succAboveOrderEmb.monotone.functor`.

It also identifies the repository fold with Mathlib's composable-arrow
representation. `composableArrows_hom_eq_composeFin` proves by induction
through `ComposableArrows.δlast` that the canonical chain `hom` is the
`composeFin` fold of its successor maps. The specialization
`adjacentChain_hom_eq_composeFin` applies this to explicit adjacent arrows.
This is a representation theorem only; it does not assume refinement
invariance.

No common-refinement theorem, descent functor, or Seifert--van Kampen result is
claimed here.
