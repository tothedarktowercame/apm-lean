# PathSubdivisionMultiplicityCommonVertices

This target constructs a sorted common vertex tuple without deduplicating
internal parameters.  It removes only the two mandatory endpoint occurrences
from each source tuple, takes the multiset sum of all remaining vertices, and
then restores one mandatory `0` and `1`.  Consequently repeated internal
vertices—including additional internal copies of `0` or `1`—are retained.

The compiled interface provides the exact length, endpoint equations,
monotonicity, and the additive multiplicity formula for every internal
parameter.  The resulting tuple has `S.n + T.n + 2` vertices.

This packet does not yet construct locator embeddings or subdivision side
labels.  The next seam is an order-preserving occurrence embedding of each
source internal list into the sorted multiset sum.  That embedding must track
occurrence ranks, not merely values, so duplicate vertices map to distinct
positions.  Once supplied, the extra occurrences from the other source can be
inserted sequentially while inheriting the split source segment's exact side
label.
