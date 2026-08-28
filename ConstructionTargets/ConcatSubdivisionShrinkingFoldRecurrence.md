# ConcatSubdivisionShrinkingFoldRecurrence

This packet proves the vertex and segment index identities at stage zero.

It also exposes the terminal-arrow orientation of `composeFin` and canonical
initial, boundary, and terminal object isomorphisms between consecutive
shrinking stages.

`terminalArrow_transport` closes the generic dependent-arrow seam: a chosen
terminal arrow conjugated by its explicit source and target equalities is the
structural last arrow. The proof eliminates the index equality before
comparing the dependent arrows.

The positive-length interface now includes `terminalPrefixVertex`,
`terminalPrefixSegment`, `terminalSegmentIndex`, and explicit source, target,
zero, and terminal endpoint equalities. These are valid for an arbitrary
`m` with `0 < m`, without requiring `m` to elaborate syntactically as a
successor.
These are the typed inputs for the next recurrence theorem.  This target does
not claim the fold equality or full right-block iteration.

The exact remaining zero-stage seam is normalization of the two `eqToHom`s in
`shrinkingPrefixArrow`: their equality proofs arise from the separately
defined vertex and segment embeddings.  Rewriting the segment equality under
the dependent arrow is rejected by Lean's motive checker, so the next theorem
must compare those endpoint transports explicitly before applying
`composeFin_reindex_of_index_eq`.

The remaining split seam is arithmetic rather than arrow transport:
`composeFin_succ` expects the positive length syntactically as `n+1`, while
the generic interface retains `m` with `0 < m`. A proof-carrying reindex of
the complete object and arrow families across `m = (m-1)+1` is still needed
before the positive-length split can specialize to the shrinking recurrence.
