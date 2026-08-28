# ConcatSubdivisionShrinkingFoldRecurrence

This packet proves the vertex and segment index identities at stage zero.

It also exposes the terminal-arrow orientation of `composeFin` and canonical
initial, boundary, and terminal object isomorphisms between consecutive
shrinking stages.

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

The attempted generic split reaches a dependent terminal-arrow seam. After
eliminating `m` as `n+1`, `terminalSegmentIndex hm = Fin.last n` is proved, but
rewriting it beneath `f` makes the surrounding categorical-composition motive
ill-typed. The missing interface is a terminal-arrow analogue of
`conjugatedArrow_compose` which simultaneously transports that arrow and the
postcomposed equality to `Fin.last m`. Only after that theorem can the split be
specialized to the shrinking recurrence.
