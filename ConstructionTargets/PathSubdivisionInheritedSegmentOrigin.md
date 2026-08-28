# PathSubdivisionInheritedSegmentOrigin

`InheritedSegmentOrigin S R` records, for every segment of `R`, an exact
source segment of `S` with the same Boolean cover label and a containing
parameter interval.

The certificate is reflexive and transitive.  A `SingleVertexInsertion`
preserves it: the two split segments inherit the split segment's label and are
bounded using the insertion's `lower` and `upper` proofs, while every other
segment retains its old endpoints.  Induction therefore equips every
`InsertionReachable S R` with the certificate.

The target specializes this result to both banked merged-vertex
reconstructions.  The remaining comparison casts their equal-size vertex
functions onto one index type, proves differently labelled common segments
lie in both cover pieces, and applies label-change evaluation invariance.
