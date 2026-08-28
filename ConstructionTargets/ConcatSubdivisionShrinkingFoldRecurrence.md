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
`successorChain_terminal_arrow_normalization` identifies that final arrow,
followed by the final-object coordinate, with literal
`f (terminalSegmentIndex hm)` and explicit endpoint transports.
These are the typed inputs for the next recurrence theorem.  This target does
not claim the fold equality or full right-block iteration.

`composeFin_eq_successorChain` completes the two fold comparisons in literal
original coordinates. `composeFin_terminal_split_of_pos` then splits the
literal original fold into the successor-shaped prefix and its terminal
transported arrow, retaining only the direct initial and final object
isomorphisms.

`composeFin_terminal_split_of_pos_literal` therefore gives the complete
positive-length split with a literal terminal arrow. The remaining seam is
specializing its successor-shaped prefix and source transport to consecutive
`shrinkingPrefixFold` stages.

`shrinkingSuccessorPrefixVertex_eq` and
`shrinkingSuccessorPrefixSegment_eq` now give the exact pointwise index
identifications for that specialization. The residual is the dependent arrow
conjugation: the endpoint transports already inside `successorChainArrow`
must be composed with those already inside the stage-`r` and stage-`r+1`
`shrinkingPrefixArrow`s before `composeFin_reindex_of_index_eq` applies.

`shrinkingPrefixFold_terminal_split_literal` performs the generic shrinking
stage specialization. `shrinkingTerminalSegment_eq_rightSegment` identifies
its terminal segment with the decreasing right-block segment under the
necessary hypothesis `r ≤ T.n`.

The weaker hypothesis `r < concatSegmentCount S T` does not imply that the
terminal arrow remains in the right block: after `r > T.n`, it lies in the
left subdivision. Thus right-suffix iteration must stop at the midpoint. The
next proof is the pointwise reindex between the displayed successor-shaped
prefix and stage `r+1`, retaining the named initial, boundary, and terminal
isomorphisms.

`shrinkingSuccessorPrefixArrow` now gives the correctly typed displayed arrow
family over stage-`r+1` segment indices.
`shrinkingSuccessorPrefixArrow_eq_conjugate` proves the pointwise comparison:
after the explicit object-coordinate transports, it is exactly the
stage-`r+1` `shrinkingPrefixArrow`.  Its proof uses the generic whiskered
conjugation-composition law, so the three independently generated endpoint
transport layers are retained until their index equalities have aligned.

`shrinkingSuccessorPrefixFold_eq` applies that pointwise comparison through
`composeFin_reindex_of_index_eq`, identifying the complete displayed prefix
with stage `r+1` while retaining both endpoint transports.

The remaining seam is matching this stage-indexed presentation with the
syntactic prefix inside `shrinkingPrefixFold_terminal_split_literal`; their
finite sizes are arithmetically equal but connected by explicit casts. No
shrinking-fold recurrence or right-segment peel beyond `r ≤ T.n` is claimed.
