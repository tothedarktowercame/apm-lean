# PathSubdivisionFullVertexOrderEmbeddings

This bounded target proves the two endpoint-separation facts needed for strict
monotonicity: every nonzero source index maps strictly above structural zero,
and every internal occurrence maps strictly below structural last.  These are
index statements, so they remain true when an internal parameter value happens
to equal `0` or `1`.

The proofs use `Fin.lastCases`, so the zero-internal-vertex case never requires
an inhabitant of `Fin 0`.

The final recovery theorems identify `mergedVertex` at every mapped source
index with the corresponding source vertex.  The remaining seam is assembling
the three adjacent-index cases (zero/internal, internal/internal, and
internal/last) into `StrictMono`; the pinned dependent `Fin.lastCases` goal does
not permit eliminating the variable projection `S.n` by a raw `cases` without
an explicit cast-normalization lemma.  Packaging the order embeddings and
their complement decomposition follows that theorem.
