# PathSubdivisionRecursiveReconstruction

This target recursively turns an endpoint-preserving finite vertex embedding
and its `RemovalDecomposition` into actual `SingleVertexInsertion` steps.

`ReconstructionResult` retains the resulting subdivision, its exact internal
vertex count, pointwise agreement with the supplied target vertex function,
and `InsertionReachable` from the source.  The successor case restricts the
target along `removed.succAbove`, recursively reconstructs the smaller target,
then uses `DeletedVertexPresentation` to reinsert the stored coordinate.

The next bounded specialization applies `reconstruct` to `mergedVertex` using
the left and right structural vertex embeddings, then compares the two
reachable subdivisions using label-change invariance.
