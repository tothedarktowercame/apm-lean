# PathSubdivisionStructuralVertexEmbeddings

This target extends the occurrence-sensitive internal embeddings to explicit
full structural vertex maps.  `leftVertexMap` and `rightVertexMap` send the
structural source endpoint `0` to merged index `0`, every internal occurrence
to its occurrence embedding shifted by one, and the structural last endpoint
to the merged last index.  Thus internal duplicate values equal to `0` or `1`
remain internal and are never substituted for the structural endpoints.

The generic `endpointExtend` construction is strictly monotone, including the
`n = 0` endpoint-only case.  It therefore packages as an order embedding.
`leftVertexEmbedding` and `rightVertexEmbedding` instantiate it with the two
occurrence embeddings.  Their endpoint and internal coordinate formulas are
explicit, and `mergedVertex_leftVertexEmbedding` and its right analogue prove
that the merged vertex sequence recovers every source vertex, including
duplicate internal values equal to `0` or `1`.

The next structural seam is a complement/insertion decomposition: enumerate
the merged indices outside either endpoint-preserving embedding and add them
one at a time while proving that each new index is bracketed by adjacent
current indices.  No such decomposition, side-label equality, or common
refinement evaluation equality is claimed here.
