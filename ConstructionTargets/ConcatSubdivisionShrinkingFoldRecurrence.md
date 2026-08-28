# ConcatSubdivisionShrinkingFoldRecurrence

This packet proves the vertex and segment index identities at stage zero.

It also exposes the terminal-arrow orientation of `composeFin` and canonical
initial/boundary object isomorphisms between consecutive shrinking stages.
These are the typed inputs for the next recurrence theorem.  This target does
not claim the fold equality or full right-block iteration.

The exact remaining zero-stage seam is normalization of the two `eqToHom`s in
`shrinkingPrefixArrow`: their equality proofs arise from the separately
defined vertex and segment embeddings.  Rewriting the segment equality under
the dependent arrow is rejected by Lean's motive checker, so the next theorem
must compare those endpoint transports explicitly before applying
`composeFin_reindex_of_index_eq`.
