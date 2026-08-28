# PathSubdivisionOccurrenceEmbeddings

This target constructs occurrence-sensitive order embeddings of the internal
vertices of each source subdivision into the multiplicity-preserving merged
internal list.

The construction does not locate vertices by value.  It proves each sorted
source list is a sublist of the sorted multiset sum, then uses Mathlib's
`sublist_iff_exists_fin_orderEmbedding_get_eq`.  Consequently repeated equal
values occupy distinct positions in source order.  The exported `get` lemmas
recover the corresponding source vertex values.

The remaining bounded step is to extend these embeddings by the structural
endpoint positions `0` and `last`, and then turn the complementary merged
positions into a one-at-a-time insertion sequence.
