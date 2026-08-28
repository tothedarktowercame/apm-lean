# ConcatSubdivisionShrinkingPrefix

This target defines proof-carrying initial embeddings after deleting `r`
terminal right-block arrows from a concatenated subdivision. Segment and
vertex embeddings preserve the underlying `Fin` value.

The terminal remaining segment is identified with the decreasing
`rightSegment`, and the terminal boundary vertex with the corresponding
`rightBlockVertex`. One-step and two-step restriction theorems show that the
family agrees with the structural `Fin.castSucc` restrictions, including the
two restrictions used by `composeFin_dropLast_two`.

The next packet can define the restricted object and arrow families by
composition with these embeddings and perform the right-to-left fold
induction. No dependent arrow is rewritten through an unresolved arithmetic
cast here.
