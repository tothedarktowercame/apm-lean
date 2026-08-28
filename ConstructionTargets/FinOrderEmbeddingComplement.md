# FinOrderEmbeddingComplement

For an order embedding `Fin (n+2) ↪o Fin (n+m+2)`, this target defines the
sorted complement of its range and proves that it has exactly `m` elements.
For endpoint-preserving embeddings it also proves that neither structural
endpoint belongs to the complement.

`removeComplementOrderIso` exposes the canonical `predAbove` transport after
removing one chosen complement index.  The remaining one-step theorem must
conjugate the old embedding through this order isomorphism, prove the chosen
index lies between adjacent old images, and show the enlarged range is the old
range plus that index.  Iterating that theorem yields the required insertion
decomposition.
