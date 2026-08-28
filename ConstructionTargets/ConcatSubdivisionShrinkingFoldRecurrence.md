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
`castIndexedComposeFin_eq` compares that cast-indexed fold with the literal
original fold while retaining explicit zero and last endpoint transports.
After eliminating positivity, only same-size casts and proof-irrelevant
equality witnesses are reduced.
`successorChain_initial_object_transport` is the matching zero-endpoint
normalization: the direct successor-source-to-zero transport followed by the
inverse cast-zero transport is exactly the source transport emitted by the
fold reindex theorem.
`successorChainComposeFin_terminal_split` supplies the literal terminal split
of the successor-shaped whole chain.
These are the typed inputs for the next recurrence theorem.  This target does
not claim the fold equality or full right-block iteration.

The remaining seam is the fully-associated calculation combining the two
fold comparisons, initial cancellation, syntactic terminal split, terminal
arrow transport, and final-object normalization. The shrinking recurrence
remains downstream of that assembly.
