# PathSubdivisionStructuralVertexEmbeddings

This target extends the occurrence-sensitive internal embeddings to explicit
full structural vertex maps.  `leftVertexMap` and `rightVertexMap` send the
structural source endpoint `0` to merged index `0`, every internal occurrence
to its occurrence embedding shifted by one, and the structural last endpoint
to the merged last index.  Thus internal duplicate values equal to `0` or `1`
remain internal and are never substituted for the structural endpoints.

The endpoint and internal coordinate formulas compile separately, including
the `n = 0` endpoint-only case.  The merged vertex function recovers every
source internal value and both structural endpoint values.

The exact remaining structural seam is proving these piecewise maps strictly
monotone across the first-internal and last-internal endpoint boundaries, then
packaging them as `Fin` order embeddings.  Internal strict monotonicity is
already supplied by the occurrence embeddings; the proof must explicitly
split the `n = 0` case rather than trying to manufacture an internal index.
Only after that can complement insertion decomposition be stated.  No order
embedding, complement decomposition, or side-label equality is claimed here.
