# PathSubdivisionMergedReconstruction

This target specializes recursive removal/reinsertion to the
multiplicity-preserving merged vertex tuple of two subordinate path
subdivisions.

`leftMergedReconstruction` starts from `S`, uses `leftVertexEmbedding`, and
produces a subdivision reachable from `S` with `S.n + T.n` internal vertices
and vertex function `mergedVertex S T`.  `rightMergedReconstruction` does the
same from `T`.  Its recursive API naturally uses the arithmetically reordered
index type `Fin (T.n + S.n + 2)`; `rightMergedTargetVertex` and
`rightMergedEmbedding` transport through `Fin.castOrderIso`, while
`rightMergedReconstruction_size_common` and
`rightMergedReconstruction_vertex` expose the result over the same
`Fin (S.n + T.n + 2)` coordinates as the left reconstruction.

The recursive result retains insertion reachability and final vertex
coordinates, but it does not retain, for each final segment, the originating
source segment whose label was inherited.  Therefore it is not yet sufficient
to prove that differing left/right labels imply membership in both cover
sets.  The next exact interface is a label-origin certificate propagated by
`reconstruct`; only after adding it can the two reconstructed subdivisions be
related by `relabelSubdivision` and `evaluate_relabel_eq`.
