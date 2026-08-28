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

`shrinkingSyntacticSuccessorPrefixFold_eq` now matches this stage-indexed
presentation with the syntactic prefix inside
`shrinkingPrefixFold_terminal_split_literal`.  It uses an explicit whole-chain
reindex; the same-size `Fin.cast` remains in the vertex map, and the endpoint
isomorphisms returned by `composeFin_reindex_of_index_eq` remain visible.

`eqToHom_three_step_coherence` proves that any three explicitly typed equality
transports agree with the direct transport having the same source and target.
`shrinkingPrefix_initial_transport_coherence` applies it to the initial end of
the three fold comparisons: the inverse successor-chain transport and the two
reindex transports compose to `shrinkingPrefixInitialIso.hom`.

`comp_eq_of_three_prefix_three_suffix` is the generic categorical assembly
lemma for the association emitted by the two fold reindexings.  It substitutes
an independently normalized three-arrow prefix and three-arrow suffix around
an unchanged middle morphism without changing any dependent transport first.
`shrinkingPrefixFold_succ` applies it to the three banked fold equalities and
the initial/terminal coherence theorems, giving the clean one-step recurrence
in terms of `shrinkingPrefixInitialIso`, `shrinkingPrefixBoundaryIso`, and
`shrinkingPrefixTerminalIso`.

`shrinkingPrefixArrow_terminal_eq_rightMappedPiece` provides the separately
typed coordinate layer under `r ≤ T.n`: the removed arrow is the actual
concatenated `mappedPiece` at `rightSegment S T ⟨T.n - r, _⟩`, surrounded by
the shrinking-prefix endpoint transports and the transports induced by the
segment-coordinate equality. `shrinkingPrefixFold_succ_right` substitutes
only that theorem into the generic recurrence. No statement peels an arrow
after the right block reaches the shared midpoint.

`shrinkingPrefixFold_rightBlockIteration` packages all and only the legal
right-block steps as a `Fin (T.n + 1)`-indexed proof family. Member `r`
instantiates the recurrence whose actual mapped piece is
`rightSegment S T ⟨T.n - r, _⟩`, so increasing indices record the removal
order. `rightBlockIteration_segment_coordinate` exposes that coordinate
independently. `shrinkingPrefixFold_rightBlockIteration_last` identifies the
last member as the step from stage `T.n` to stage `T.n + 1`, and
`rightBlockIteration_stops_at_midpoint` records that stopping index. There is
no recurrence member at the midpoint or beyond it. The finite proof family is
intended for the next heterogeneous fold that combines
`rightBlockComposeFin_eq` with the stage-zero comparison; it does not assume
that composite.

`reverseRemovalStage_segment_coordinate` makes the order conversion explicit:
removal stage `T.n-j` is forward right-block segment `j`.
`reverseRemovalStage_terminalArrow_eq_rightMappedPiece` specializes the banked
terminal-arrow theorem at that reverse stage, retaining its complete endpoint
conjugation and the actual concatenated mapped piece. Finally,
`rightSuffixAccum_full_unfold` shows that the full accumulator begins with
stage `T.n` (therefore forward segment zero) and then recurses through the
shorter accumulator. Together these declarations certify the forward order
`0, ..., T.n` while the recursive stage indices run `T.n, ..., 0`.

The remaining comparison with `rightBlockComposeFin_eq` is a genuinely
dependent reverse-index fold theorem: it must compose the boundary/terminal
isomorphisms between successive removal stages and show that their internal
`eqToHom`s cancel to the structural `rightBlockObject` endpoints. No such
finite conjugation theorem is yet present, so no accumulator/right-block fold
equality or concatenated segment-fold formula is claimed here.

`reverseRightStage` assigns forward right-block vertex `j` to removal stage
`T.n+1-j`. Its zero, last, `castSucc`, and `succ` theorems state the midpoint,
terminal, source-stage, and target-stage coordinates separately.
`reverseRightTerminalVertex_eq_rightBlockVertex` proves that the terminal
vertex of this removal stage is literally the ambient right-block vertex;
the proof uses index arithmetic and does not identify dependent objects by
definition. `reverseRightObject` and `reverseRightObjectIso` lift that equality
to the requested objectwise comparison, with explicit zero and last formulas.

`eqToHom_three_step_whisker_arrow` supplies the generic terminal-side
normalization without moving the dependent arrow.
`shrinkingPrefix_terminal_transport_coherence` applies it to the two inverse
reindex transports, the literal split's source transport, the terminal arrow,
and its final transport.  The result is exactly
`shrinkingPrefixBoundaryIso.hom`, the unchanged terminal arrow, and
`shrinkingPrefixTerminalIso.hom`.

`rightRemovalStep` packages one legal stage morphism, including its named
boundary and terminal transports. `rightInitialAccum` and `rightSuffixAccum`
are proof-carrying heterogeneous composites: the former accumulates the
initial-object transports, while the latter recursively prepends the removal
at stage `k`. Thus the midpoint suffix records precisely the removal order
`T.n, ..., 0`; every contained terminal arrow is identified with the actual
right-block mapped piece by
`shrinkingPrefixArrow_terminal_eq_rightMappedPiece`.

`shrinkingPrefixFold_rightBlockAccum` proves the finite comparison at every
stage `k <= T.n + 1`. `shrinkingPrefixFold_zero_eq_midpoint` specializes it
after exactly all legal right-block removals, without invoking a recurrence at
the midpoint. `concatComposeFin_eq_midpoint_rightAccum` then uses
`shrinkingPrefixFold_zero` to connect this comparison to the literal full
concatenated segment fold, retaining its endpoint transports.

`reverseRemovalStage_terminalArrow_eq_rightMappedPiece` now states its result
directly at forward coordinate `j`; it no longer leaves the dependent segment
`T.n - (T.n - j)` in the mapped-piece term. `reverseRightArrow` packages the
actual removal step as a forward-indexed heterogeneous chain, using
`reverseRightStage_castSucc` and `reverseRightStage_succ` at its endpoints.

`reverseRemovalStage_sourceVertex_eq_rightSegment` and
`reverseRemovalStage_targetVertex_eq_rightSegment` now prove those two ambient
endpoint equalities by composing the shrinking endpoint theorem with the
banked reverse-stage segment coordinate. `reverseRemovalStageSourceIso` and
`reverseRemovalStageTargetIso` lift them through the actual ambient-point
object family.

`eqToHom_four_four_eq_two_two_conjugation` names every intermediate source and
target object and proves the required multi-transport cancellation without
simplifying dependent arrows. `reverseRightArrow_eq_conjugate` applies it to
the arithmetic-stage, boundary, segment-endpoint, terminal, and right-block
transports.

`reverseRightComposeFin_eq` then applies the generic dependent finite-fold
conjugation theorem. The reverse-stage chain is the actual forward right-block
fold, bracketed only by `reverseRightObjectIso` at its midpoint and terminal
objects. The remaining seam is recursive: identify `rightSuffixAccum` with
this `reverseRightArrow` `composeFin`, including its zero and successor reindex
equations. No accumulator equality is claimed yet.

`rightSuffixSliceVertex` and `rightSuffixSliceSegment` now select the terminal
`k` arrows of that forward chain. `rightSuffixSliceArrow` retains the two
proof-carrying endpoint transports into the actual `reverseRightArrow`, and
`rightSuffixSliceFold` is their dependent composite. The zero fold and the
successor coordinate equations compile: the new first segment is coordinate
`T.n-k`, while the remaining vertex and segment tails are exactly the previous
`k`-slice.

The next theorem must turn those coordinate equations into a head-split law
for `rightSuffixSliceFold (k+1)`. Mathlib's banked `composeFin_succ` exposes
the final arrow, whereas this slice grows by prepending its first arrow. A
proof-carrying front/tail reindex is therefore still required before the
recursive equation can be matched with `rightSuffixAccum_succ`.

`reverseRightAccumSourceIso` and `reverseRightAccumTargetIso` provide the two
outer coordinates for that bridge. They identify the reverse fold at zero and
`Fin.last` with accumulator stages `T.n+1` and zero; their `_hom` theorems
expose the exact equality transports.

The remaining comparison requires a generalized dependent interval fold.
`rightSuffixAccum (k+1)` prepends removal step `k`, while `composeFin_succ`
peels the final forward arrow. Induction therefore needs the slice of
`reverseRightArrow` corresponding to removal stages `k-1, ..., 0`, together
with its transported endpoints. The current `composeFin` API has no such
offset/slice family. No equality with `rightSuffixAccum`, and consequently no
combined concatenated-fold formula, is assumed here.

`rightSuffixSlice_source_stage` and `rightSuffixSlice_target_stage` now prove
the induction invariant's two endpoint coordinates for every slice length
`k`. `rightSuffixSliceSourceIso` and `rightSuffixSliceTargetIso` retain those
coordinates as explicit object transports. The base bridge
`rightSuffixSliceFold_zero_eq_accum` compiles with both endpoint isomorphisms;
it does not obtain the equality by treating the two proof witnesses as
definitionally equal.

`composeFin_front_split` supplies the generic first-arrow recursion, and
`rightSuffixSliceFold_succ_front` specializes it to the `(k+1)` slice.
`rightSuffixSliceArrow_succ_tail_eq_conjugate` aligns every successor-tail
arrow with the corresponding `k`-slice arrow, including both endpoint
transports. `rightSuffixSliceTailFold_eq` applies the dependent reindex theorem
to the whole tail, and `rightSuffixSliceFold_succ` gives the resulting
successor recurrence with only the first arrow and the two outer tail
transports exposed.

`rightRemovalStep_conjugation` transports a removal arrow across an equality
of arithmetic stages without rewriting beneath its dependent source and
target. Using it, `rightSuffixSlice_front_source_coherence` identifies the
first slice arrow and tail-source transport with `rightRemovalStep k` between
the named source coordinates. `rightSuffixSlice_target_coherence` performs
the corresponding terminal normalization.

`rightSuffixSliceFold_eq_accum` proves by finite induction that every slice
fold is `rightSuffixAccum`, bracketed by `rightSuffixSliceSourceIso` and
`rightSuffixSliceTargetIso`. At full length,
`rightSuffixSliceVertex_full` and `rightSuffixSliceSegment_full` give the
proof-carrying pointwise identity coordinates. The arrow comparison
`rightSuffixSliceArrow_full_eq_conjugate` and dependent reindex theorem then
yield `rightSuffixSliceFold_full_eq`.

`rightSuffixAccum_full_eq_reverseRight` combines the full slice with the
accumulator induction. `rightSuffixAccum_full_eq_rightBlock` continues through
`reverseRightComposeFin_eq` and `rightBlockComposeFin_eq`, so the central fold
is literally the original subdivision `T`'s mapped-piece fold.
`concatComposeFin_eq_midpoint_rightBlock` substitutes that result into the
full concatenated fold comparison. It deliberately retains every midpoint,
reverse-chain, right-block, and terminal endpoint transport.

For the remaining left prefix, `midpointLeftSegmentIndex` and
`midpointLeftVertexIndex` give explicit casts from the original `S` indices
into the subtraction-indexed midpoint stage.
`midpointLeftSegmentEmbedding_eq` proves that every such segment is the
literal `leftSegment`; `midpointLeftPoint_eq` and its `castSucc`/`succ` forms
identify every midpoint object with the corresponding `S.point` object.

`shrinkingPrefixArrow_midpointLeft_eq_conjugate` now conjugates every displayed
midpoint arrow through these endpoint equalities and
`mappedPiece_concat_left`. `midpointLeftReindexedFold_eq` applies
`composeFin_reindex_of_index_eq`, identifying the entire midpoint fold
displayed through `midpointLeftVertexIndex` with the literal `S` fold.

`midpointLeftLength_eq` names the arithmetic equality without eliminating it
inside the specialized chain. Its segment and vertex coordinate lemmas
identify the pre-existing midpoint casts with the generic `castChainSegment`
and `castChainVertex` interface. `midpointLeftDisplayedFold_eq_literal` then
applies `composeFin_cast_reindex`: the displayed original-left-cardinality
fold is the literal `shrinkingPrefixFold D S T (T.n+1)`, bracketed by its
explicit zero and final object transports.

`shrinkingPrefixFold_midpoint_eq_leftFold` now combines the two displayed-fold
equalities. It expresses the literal midpoint `shrinkingPrefixFold` as the
literal `S` mapped-piece fold with all four zero/final transports retained;
`five_morphism_reassociation` supplies only the required categorical
parenthesization.

The next seam is normalization of `rightInitialAccum (T.n+1)` against the
source transports of this theorem, followed by cancellation of the midpoint
and terminal transport chain in `concatComposeFin_eq_midpoint_rightBlock`
against the outer maps in `evaluate`. No evaluation-composition theorem is
claimed yet.
