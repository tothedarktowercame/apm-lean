# EndpointPreservingFinEmbeddingRemoval

This target gives one recursive removal step for finite order embeddings with
distinguished endpoints.  A point outside the embedding range is deleted using
Mathlib's `Fin.succAboveOrderIso`; the resulting embedding has a codomain one
element smaller, still maps first to first and last to last, and reinsertion by
`succAbove` recovers the original embedding pointwise and on ranges.

`EndpointRemovalStep.pivot` identifies the coordinate immediately before the
removed point.  Reinsertion places the removed point strictly between the
images of that pivot and its successor.  The parameterization uses codomain
`Fin (n + k + 3)` so the smaller codomain is definitionally
`Fin (n + k + 2)` and no truncated subtraction is involved.

The next seam is an induction over a chosen enumeration of the complement.
At each stage it must relate the current pivot to the subdivision segment and
side label being split.  This target does not claim that complement induction,
an insertion-reachability certificate, or common-refinement invariance.
