# EndpointPreservingFinEmbeddingDecomposition

This target recursively removes every complementary codomain index from an
endpoint-preserving `Fin` order embedding.  The base self-embedding is proved
equal to the identity.  Each successor node stores an `EndpointRemovalStep`,
including the exact removed codomain coordinate, and recursively decomposes
its smaller embedding.

The pivot normalization proves
`removalPivotNext.castSucc = pivot.succ`, and the left reinsertion equation
identifies the coordinate immediately before the removed point. Together with
`EndpointRemovalStep.reinsert_smaller` and the existing strict inequalities,
the recursive nodes retain the coordinates needed to construct a
`SingleVertexInsertion`.

The remaining layer transports vertex values and side-membership certificates
through each stored removal step and packages the reconstruction as an actual
subdivision insertion sequence.
