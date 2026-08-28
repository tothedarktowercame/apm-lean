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
`successorChainVertex`, `successorChainSegment`, and `successorChainArrow`
now package the complete chain in the syntactic successor sizes
`Fin ((m-1)+2)` and `Fin ((m-1)+1)`, with explicit endpoint equalities.
`successorChainCastLast_eq_last` identifies its cast structural last vertex
with literal `Fin.last m`; `successorChain_final_object_transport` composes the
two resulting object transports into one explicit equality transport.
`successorChainComposeFin_eq` compares its total fold with the proof-carrying
reindex of the original fold. The arrow comparison never rewrites the
terminal index beneath the dependent family.
These are the typed inputs for the next recurrence theorem.  This target does
not claim the fold equality or full right-block iteration.

The remaining seam is normalization from the reindexed fold to the literal
original fold. Its final object uses a cast of the structural last index,
whereas the literal fold ends at `Fin.last m`. That endpoint transport must
be combined with `terminalArrow_transport` before the shrinking recurrence.
