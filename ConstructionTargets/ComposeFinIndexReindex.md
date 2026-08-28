# ComposeFinIndexReindex

This target gives proof-carrying reindexing for dependent finite categorical
chains. Pointwise index equality is converted to typed `eqToIso`s at objects;
successor-arrow compatibility is required only after those isomorphisms align
the endpoints. `composeFin_reindex_of_index_eq` then applies the banked
conjugation theorem, so internal transports cancel.

`castChainVertex` and `castChainSegment` represent a chain through a
propositionally equal length. `composeFin_cast_reindex` is the corresponding
cross-cardinality theorem: callers provide the cast-indexed arrows with their
endpoint conjugations, and the total comparison retains only explicit zero
and final object isomorphisms. The length equality is eliminated only inside
this generic theorem, before any problem-specific dependent family exists.

`succ_castSucc_eq_castSucc_succ` and `frontRecursionObjectIso` certify the
specific front-recursion equality that blocked the append proof. No dependent
arrow family is rewritten by raw `congrArg`.

The remaining concatenation work is an induction splitting the segment index
at `S.n + 1`, applying this reindex theorem to its recursive prefix, and then
using `mappedPiece_concat_left/right`. The final midpoint and evaluation
endpoint cancellation is not claimed here.
